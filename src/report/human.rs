//! The report as notes of the compiler, one per function and one per loop, at its span.

use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::chc;

use super::constraints::{Annotation, Constraint};
use super::failure::Failure;
use super::formula::Formula;
use super::sites::{Names, Site, SiteKind};
use super::solution::{block_template, invariant, over, signature, Solution};
use super::{assumed, constraint_of, location, Entry, Items};

pub(super) fn constraint_line(tcx: TyCtxt<'_>, c: &Constraint) -> String {
    let at = c
        .span
        .map(|span| format!(" ({})", location(tcx, span)))
        .unwrap_or_default();
    format!("{:?} {}{at}: {}", c.id, c.kind, c.formula)
}

pub(super) struct Human<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) items: Items,
    pub(super) names: &'a Names,
    pub(super) solution: Result<Solution, String>,
    /// Whether the parts are solved on their own (`THRUST_SPLIT`), each refuted part with a
    /// refutation of its own.
    pub(super) split: bool,
}

impl Human<'_, '_> {
    fn site_notes(&self, notes: &mut Vec<String>, entry: &Entry<'_>, site: &Site) {
        // Without a solution, a site has only its template to show, if that was asked for.
        let solved = self.solution.as_ref().is_ok_and(|s| s.solves(site));
        if !solved && !self.items.template {
            return;
        }
        let lines = match (site.kind, site.signature) {
            (SiteKind::Contract, _) => self.contract_lines(entry, site),
            (_, Some(_)) => self.signature_lines(site),
            (_, None) => self.block_lines(site),
        };
        if lines.is_empty() {
            return;
        }
        let title = match site.kind {
            SiteKind::Contract => "contract (inferred)".to_owned(),
            SiteKind::Loop(_) => "invariant (inferred)".to_owned(),
            SiteKind::Block(bb) => format!("type of {bb:?}"),
        };
        notes.push(format!("{title}\n{}", lines.join("\n")));
    }

    /// The solution of `site`, or why there is none when one is asked for.
    fn solution(&self, site: &Site, lines: &mut Vec<String>) -> Option<&Solution> {
        let solution = match &self.solution {
            Ok(solution) => match solution.unsolved(site) {
                Some(why) => Err(why),
                None => Ok(solution),
            },
            Err(why) => Err(why.as_str()),
        };
        match solution {
            Ok(solution) => Some(solution),
            Err(why) => {
                if self.items.solution || self.items.inferred {
                    lines.push(why.to_owned());
                }
                None
            }
        }
    }

    fn contract_lines(&self, entry: &Entry<'_>, site: &Site) -> Vec<String> {
        let mut lines = Vec::new();
        if self.items.template {
            let template = signature(&entry.name, site, self.names, &Formula::clone);
            lines.push(format!("template: {template}"));
        }
        let Some(solution) = self.solution(site, &mut lines) else {
            return lines;
        };
        if self.items.solution {
            let solved = solution.lines(site, self.names);
            lines.push(format!("solution: {}", solved.join("\n          ")));
        }
        if self.items.inferred {
            let inferred = signature(&entry.name, site, self.names, &|f| solution.apply(f));
            lines.push(format!("inferred: {inferred}"));
        }
        lines
    }

    /// A template that is one predicate variable: its signature, then its interpretation.
    fn signature_lines(&self, site: &Site) -> Vec<String> {
        let mut lines = Vec::new();
        if self.items.template || self.items.solution || self.items.inferred {
            lines.push(block_template(site, self.names));
        }
        let Some(solution) = self.solution(site, &mut lines) else {
            return lines;
        };
        if !(self.items.solution || self.items.inferred) {
            return lines;
        }
        if site.signature.is_some_and(|p| solution.interprets(p)) {
            let inferred = invariant(site, self.names, &|f| solution.apply(f));
            lines.push(format!(":= {inferred}"));
        } else {
            lines.push(
                "not in the query: `true` if no constraint depends on it, `false` if none \
                 establishes it"
                    .to_owned(),
            );
        }
        lines
    }

    fn block_lines(&self, site: &Site) -> Vec<String> {
        let mut lines = Vec::new();
        if self.items.template {
            lines.push(format!("template: {}", block_template(site, self.names)));
        }
        let Some(solution) = self.solution(site, &mut lines) else {
            return lines;
        };
        if self.items.solution {
            let solved = solution.lines(site, self.names);
            lines.push(format!("solution: {}", solved.join("\n          ")));
        }
        if self.items.inferred {
            let formula = invariant(site, self.names, &|f| solution.apply(f));
            lines.push(format!("inferred: |{}| {formula}", over(site)));
        }
        lines
    }

    fn constraint_notes(&self, notes: &mut Vec<String>, constraints: &[Constraint]) {
        if !self.items.constraints || constraints.is_empty() {
            return;
        }
        let lines: Vec<_> = constraints
            .iter()
            .map(|c| format!("  {}", constraint_line(self.tcx, c)))
            .collect();
        notes.push(format!("constraints from this code:\n{}", lines.join("\n")));
    }

    /// Emits one note at `span` carrying `notes`, if there are any.
    fn note(&self, span: Span, title: String, notes: Vec<String>) {
        if notes.is_empty() {
            return;
        }
        let mut diag = self.tcx.dcx().struct_span_note(span, title);
        for note in notes {
            diag.note(note);
        }
        diag.emit();
    }

    /// The refuted goal at its span, with the run reaching it.
    pub(super) fn failure(
        &self,
        answer: &chc::Answer,
        asked: Option<&super::Asked>,
        part_note: Option<String>,
        failure: Option<&Failure>,
        entries: &[Entry<'_>],
    ) {
        let unsat = matches!(answer.result, Err(chc::CheckSatError::Unsat));
        if !self.items.failure || !asked.map_or(unsat, |a| a.refuted) {
            return;
        }
        if let (Some(asked), false) = (asked, unsat) {
            self.tcx.dcx().note(format!(
                "thrust: no failing obligation to show for part {}: the second run, asked for a \
                 refutation, gave none ({})",
                asked.part,
                chc::verdict(&answer.result)
            ));
            return;
        }
        let Some(failure) = failure else {
            let refused = answer.z3_refused.as_deref().unwrap_or("none");
            let why = match (&answer.proof, answer.goal_markers.is_empty()) {
                (None, true) => "the solver gives no refutation, and `z3`, asked in its place, \
                                 does not read the query (it has forall sorts or sequences)"
                    .to_owned(),
                // A `sat` here contradicts the solver's verdict.
                (None, false) if answer.proof_by_z3 && refused == "sat" => {
                    "`z3`, asked for the run as the solver gives none, answers `sat`: the two \
                     solvers disagree on the query"
                        .to_owned()
                }
                (None, false) if answer.proof_by_z3 => format!(
                    "`z3`, asked for the run as the solver gives none, gave none ({refused})"
                ),
                (None, false) => {
                    format!("the second run, asked for a refutation, gave none ({refused})")
                }
                (Some(_), _) => "the refutation derives no goal of the system".to_owned(),
            };
            let part = asked
                .map(|a| format!(" for part {}", a.part))
                .unwrap_or_default();
            self.tcx.dcx().note(format!(
                "thrust: no failing obligation to show{part}: {why}"
            ));
            return;
        };
        let found = constraint_of(entries, failure.goal);
        let title = match found {
            Some((entry, c)) => format!("thrust: refuted: {} in `{}`", c.kind, entry.name),
            None => format!("thrust: refuted: {:?}", failure.goal),
        };
        let mut notes = Vec::new();
        if let Some((_, c)) = found {
            notes.push(format!("{:?}: {}", c.id, c.formula));
            let values: Vec<String> = failure
                .named_values(c)
                .into_iter()
                .map(|(name, value)| format!("{name} = {value}"))
                .collect();
            if !values.is_empty() {
                notes.push(format!("where it fails: {}", values.join(", ")));
            }
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
        // A goal over no unknown fails by its constraint alone, without a run.
        if !lines.is_empty() {
            let who = match failure.by_z3 {
                true => "`z3` (asked for the run, as the solver gives none)",
                false => "the solver",
            };
            notes.push(format!(
                "how {who} reaches it: each fact follows, by the constraint in brackets, \
                 from the facts indented under it (a derivation, not an order of execution):\n{}",
                lines.join("\n")
            ));
        }
        let inferred: Vec<String> = failure
            .inferred
            .iter()
            .filter_map(|def| entries.iter().find(|e| e.def == *def))
            .map(|e| format!("`{}`", e.name))
            .collect();
        if !inferred.is_empty() {
            notes.push(format!(
                "it goes through the contract inferred for {}: a wrong result there shows here",
                inferred.join(", ")
            ));
        }
        let assumed: Vec<String> = assumed(self.tcx, entries, failure)
            .into_iter()
            .map(|(name, span)| format!("`{name}` ({})", location(self.tcx, span)))
            .collect();
        if !assumed.is_empty() {
            notes.push(format!(
                "it assumes the written contract of {}: a wrong `ensures` there shows here",
                assumed.join(", ")
            ));
        }
        if !self.split {
            notes.push(
                "the solver refutes one obligation of a query: others may fail too \
                 (`THRUST_SPLIT` refutes one in each part)"
                    .to_owned(),
            );
        }
        notes.extend(part_note);
        let checked = match found.map(|(_, c)| &c.annotation) {
            Some(Annotation::Checks(spans)) => spans.as_slice(),
            _ => &[],
        };
        // At the obligation, the refutation is the verification error (see `super::Refuted`).
        match found.and_then(|(_, c)| c.error_span) {
            Some(span) => {
                let message = format!("verification error: Unsat ({title})");
                let mut diag = self.tcx.dcx().struct_span_err(span, message);
                // Which of several clauses fails, the refutation does not say.
                let label = if checked.len() > 1 {
                    "a clause of the annotation it checks"
                } else {
                    "the annotation it checks"
                };
                for annotation in checked {
                    diag.span_label(*annotation, label);
                }
                for note in notes {
                    diag.note(note);
                }
                diag.emit();
            }
            None => {
                let mut diag = match entries.first() {
                    Some(entry) => self.tcx.dcx().struct_span_note(entry.span, title),
                    None => self.tcx.dcx().struct_note(title),
                };
                for note in notes {
                    diag.note(note);
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
