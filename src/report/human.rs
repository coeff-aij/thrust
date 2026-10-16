//! The report as notes of the compiler, one per function and one per loop, at its span.

use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::chc;

use super::constraints::Constraint;
use super::expr::Expr;
use super::failure::Failure;
use super::sites::{Names, Site, SiteKind};
use super::solution::{contract_help, invariant, over, signature, Solution};
use super::{constraint_of, location, Entry, Items};

pub(super) fn constraint_line(tcx: TyCtxt<'_>, c: &Constraint) -> String {
    let at = c
        .span
        .map(|span| format!(" ({})", location(tcx, span)))
        .unwrap_or_default();
    format!("{:?} {}{at}: {}", c.id, c.kind, c.formula())
}

pub(super) struct Human<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) items: Items,
    pub(super) names: &'a Names,
    pub(super) solution: Result<Solution, &'static str>,
}

impl Human<'_, '_> {
    fn site_notes(&self, notes: &mut Vec<Note>, entry: &Entry<'_>, site: &Site) {
        let id = |e: &Expr| e.clone();
        let is_contract = site.kind == SiteKind::Contract;
        let mut lines = Vec::new();
        if self.items.template {
            let template = if is_contract {
                signature(&entry.name, site, &id)
            } else {
                invariant(site, &id).to_string()
            };
            lines.push(format!("template: {template}"));
        }
        let wants_solution = self.items.solution || self.items.inferred;
        let solution = match &self.solution {
            Ok(solution) => Some(solution),
            Err(why) => {
                if wants_solution {
                    lines.push((*why).to_owned());
                }
                None
            }
        };
        if let (Some(solution), true) = (solution, self.items.solution) {
            let solved = solution.lines(site, self.names);
            lines.push(format!("solution: {}", solved.join("\n          ")));
        }
        if let (Some(solution), true) = (solution, self.items.inferred) {
            let apply = |e: &Expr| solution.apply(e);
            let inferred = if is_contract {
                signature(&entry.name, site, &apply)
            } else {
                invariant(site, &apply).to_string()
            };
            lines.push(format!("inferred: {inferred}"));
        }
        if lines.is_empty() {
            return;
        }
        if !is_contract {
            lines.insert(0, format!("over: {}", over(site)));
        }
        let title = match site.kind {
            SiteKind::Contract => "contract (inferred)".to_owned(),
            SiteKind::Loop(_) => "invariant (inferred)".to_owned(),
            SiteKind::Block(bb) => format!("type of {bb:?}"),
        };
        notes.push(Note::Note(format!("{title}\n{}", lines.join("\n"))));
        if let (Some(solution), true) = (solution, self.items.inferred && is_contract) {
            if let Some(help) = contract_help(site, solution) {
                notes.push(Note::Help(help));
            }
        }
    }

    fn constraint_notes(&self, notes: &mut Vec<Note>, constraints: &[Constraint]) {
        if !self.items.constraints || constraints.is_empty() {
            return;
        }
        let lines: Vec<_> = constraints
            .iter()
            .map(|c| format!("  {}", constraint_line(self.tcx, c)))
            .collect();
        notes.push(Note::Note(format!(
            "constraints from this code:\n{}",
            lines.join("\n")
        )));
    }

    /// Emits one note at `span` carrying `notes`, if there are any.
    fn note(&self, span: Span, title: String, notes: Vec<Note>) {
        if notes.is_empty() {
            return;
        }
        let mut diag = self.tcx.dcx().struct_span_note(span, title);
        for note in notes {
            match note {
                Note::Note(text) => diag.note(text),
                Note::Help(text) => diag.help(text),
            };
        }
        diag.emit();
    }

    /// The refuted goal at its span, with the run reaching it.
    pub(super) fn failure(
        &self,
        answer: &chc::Answer,
        failure: Option<&Failure>,
        entries: &[Entry<'_>],
    ) {
        if !self.items.failure || !matches!(answer.result, Err(chc::CheckSatError::Unsat)) {
            return;
        }
        let Some(failure) = failure else {
            let why = if answer.proof.is_none() {
                "the solver gave no refutation (only `z3` is asked for one)"
            } else {
                "the refutation derives no goal of the system"
            };
            self.tcx
                .dcx()
                .note(format!("thrust: no failing obligation to show: {why}"));
            return;
        };
        let found = constraint_of(entries, failure.goal);
        let title = match found {
            Some((entry, c)) => format!("thrust: refuted: {} in `{}`", c.kind, entry.name),
            None => format!("thrust: refuted: {:?}", failure.goal),
        };
        let mut notes = Vec::new();
        if let Some((_, c)) = found {
            notes.push(Note::Note(format!("{:?}: {}", c.id, c.formula())));
        }
        let mut lines = Vec::new();
        for step in &failure.run {
            let via = step
                .via
                .and_then(|id| constraint_of(entries, id))
                .map(|(_, c)| {
                    let at = c.span.map(|s| format!(", {}", location(self.tcx, s)));
                    format!("   [{:?} {}{}]", c.id, c.kind, at.unwrap_or_default())
                })
                .unwrap_or_default();
            lines.push(format!("{}{}{via}", "  ".repeat(step.depth + 1), step.fact));
        }
        if failure.truncated {
            lines.push("  …".to_owned());
        }
        notes.push(Note::Note(format!(
            "a run reaching it, from the solver's refutation (each fact above the ones it is \
             derived from):\n{}",
            lines.join("\n")
        )));
        let span = found
            .and_then(|(_, c)| c.span)
            .or_else(|| entries.first().map(|e| e.span));
        match span {
            Some(span) => self.note(span, title, notes),
            None => {
                let mut diag = self.tcx.dcx().struct_note(title);
                for note in notes {
                    if let Note::Note(text) = note {
                        diag.note(text);
                    }
                }
                diag.emit();
            }
        }
    }

    pub(super) fn emit(&self, entries: &[Entry<'_>]) {
        for entry in entries {
            let mut notes = Vec::new();
            if let Some(site) = &entry.contract {
                self.site_notes(&mut notes, entry, site);
            }
            if self.items.internal {
                for site in &entry.blocks {
                    self.site_notes(&mut notes, entry, site);
                }
            }
            self.constraint_notes(&mut notes, &entry.constraints);
            self.note(entry.span, format!("thrust: `{}`", entry.name), notes);

            for (header, (site, constraints)) in &entry.loops {
                let span = site
                    .as_ref()
                    .map(|s| s.span)
                    .or_else(|| entry.body.span(*header, None))
                    .unwrap_or(entry.span);
                let mut notes = Vec::new();
                if let Some(site) = site {
                    self.site_notes(&mut notes, entry, site);
                }
                self.constraint_notes(&mut notes, constraints);
                self.note(span, format!("thrust: loop in `{}`", entry.name), notes);
            }
        }
    }
}

enum Note {
    Note(String),
    Help(String),
}
