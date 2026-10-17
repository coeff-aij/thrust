//! The parts of a system solved on their own (`THRUST_SPLIT`) as the output names them: each
//! by its number and the code its clauses come from, with its verdict.

use std::collections::{BTreeMap, HashMap};

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::Span;

use crate::chc;

use super::constraints::Provenance;
use super::file_name;

/// A part of the system solved on its own.
pub struct Part {
    /// Its number among the parts, from 1.
    pub id: usize,
    pub clauses: usize,
    /// The functions its clauses come from, in the order of their code.
    pub functions: Vec<PartCode>,
    /// See [`chc::verdict`].
    pub verdict: &'static str,
    /// Whether the verdict was that of an earlier run (`THRUST_CACHE_DIR`).
    pub cached: bool,
}

/// The verdict of the crate from those of its parts: `unsat` if a part is, else the first that
/// is not `sat`.
pub fn crate_verdict(verdicts: &[&'static str]) -> &'static str {
    if verdicts.contains(&"unsat") {
        return "unsat";
    }
    verdicts
        .iter()
        .copied()
        .find(|v| *v != "sat")
        .unwrap_or("sat")
}

/// A function some clauses of a part come from, and the code they were made at, from the first
/// to the last.
pub struct PartCode {
    pub r#fn: String,
    pub span: Span,
}

impl Part {
    pub fn new(tcx: TyCtxt<'_>, system: &chc::System, index: usize, part: &chc::Part) -> Self {
        Part {
            id: index + 1,
            clauses: part.clauses.len(),
            functions: code(tcx, system, &part.clauses),
            verdict: chc::verdict(&part.result),
            cached: part.cached,
        }
    }

    /// `` `f` (a.rs:3-6), `g` (a.rs:9) ``.
    fn functions(&self, tcx: TyCtxt<'_>) -> String {
        if self.functions.is_empty() {
            return "no function".to_owned();
        }
        let named: Vec<String> = self
            .functions
            .iter()
            .map(|f| format!("`{}` ({})", f.r#fn, lines(tcx, f.span)))
            .collect();
        named.join(", ")
    }

    /// What the error of a part that fails says of it.
    pub fn error_note(&self, tcx: TyCtxt<'_>, parts: usize) -> String {
        let clauses = match self.clauses {
            1 => "1 clause".to_owned(),
            n => format!("{n} clauses"),
        };
        format!(
            "in part {} of {parts}, of {clauses} from {}",
            self.id,
            self.functions(tcx)
        )
    }
}

/// The functions the clauses `ids` come from, each with the code its clauses were made at.
fn code(tcx: TyCtxt<'_>, system: &chc::System, ids: &[chc::ClauseId]) -> Vec<PartCode> {
    let mut spans: HashMap<LocalDefId, Span> = HashMap::new();
    for &id in ids {
        let provenance = Provenance::of(&system.clauses[id].debug_info);
        let (Some(def), Some(span)) = (provenance.def, provenance.span(tcx)) else {
            continue;
        };
        let all = spans.entry(def).or_insert(span);
        *all = all.to(span);
    }
    let mut code: Vec<PartCode> = spans
        .into_iter()
        .map(|(def, span)| PartCode {
            r#fn: tcx.def_path_str(def.to_def_id()),
            span,
        })
        .collect();
    code.sort_by_key(|c| c.span.lo());
    code
}

/// `file:first-last` of the lines of `span`, or `file:line`.
fn lines(tcx: TyCtxt<'_>, span: Span) -> String {
    let source_map = tcx.sess.source_map();
    let first = source_map.lookup_char_pos(span.lo()).line;
    let last = source_map.lookup_char_pos(span.hi()).line;
    if last > first {
        format!("{}:{first}-{last}", file_name(tcx, span))
    } else {
        format!("{}:{first}", file_name(tcx, span))
    }
}

/// At most this many of the parts solved now are named.
const SOLVED_SHOWN: usize = 5;

/// The notes after the errors of the parts: how many were solved and which of them now, and the
/// functions of a failing part whose clauses fall into more than one part, with why.
pub fn emit_notes(tcx: TyCtxt<'_>, parts: &[Part]) {
    let cached = parts.iter().filter(|p| p.cached).count();
    let solved: Vec<String> = parts
        .iter()
        .filter(|p| !p.cached)
        .map(|p| format!("part {} from {}", p.id, p.functions(tcx)))
        .collect();
    let mut note = match parts.len() {
        1 if cached == 1 => "thrust: 1 part solved on its own, from an earlier run".to_owned(),
        1 => "thrust: 1 part solved on its own".to_owned(),
        n => format!("thrust: {n} parts solved on their own, {cached} of them from earlier runs"),
    };
    if !solved.is_empty() && cached > 0 {
        let more = solved.len().saturating_sub(SOLVED_SHOWN);
        let shown = &solved[..solved.len() - more];
        note.push_str(&format!("; solved now: {}", shown.join("; ")));
        if more > 0 {
            note.push_str(&format!(" and {more} more"));
        }
    }
    tcx.dcx().note(note);

    // Said where it explains a failing part's error.
    let failing: Vec<&str> = parts
        .iter()
        .filter(|p| p.verdict != "sat")
        .flat_map(|p| p.functions.iter().map(|f| f.r#fn.as_str()))
        .collect();
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for f in parts.iter().flat_map(|p| &p.functions) {
        *counts.entry(&f.r#fn).or_default() += 1;
    }
    let split: Vec<String> = counts
        .into_iter()
        .filter(|(f, n)| *n > 1 && failing.contains(f))
        .map(|(f, n)| format!("`{f}` in {n}"))
        .collect();
    if split.is_empty() {
        return;
    }
    tcx.dcx().note(format!(
        "thrust: a function can be in several parts: {}. Its clauses fall apart where they share \
         no unknown, as on the two sides of a written annotation (a contract, an `invariant!`, a \
         refined type), and a clause with no unknown is a part of its own",
        split.join(", ")
    ));
}

#[cfg(test)]
mod tests {
    use super::crate_verdict;

    #[test]
    fn a_refuted_part_refutes_the_crate_before_a_timeout() {
        assert_eq!(crate_verdict(&["sat", "timeout", "unsat"]), "unsat");
        assert_eq!(crate_verdict(&["sat", "timeout", "sat"]), "timeout");
        assert_eq!(crate_verdict(&["sat", "sat"]), "sat");
    }
}
