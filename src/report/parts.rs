//! The parts of a system solved on their own (`THRUST_SPLIT`) as the output names them: each
//! by its number and the code its clauses come from, with its verdict.

use std::collections::{BTreeMap, HashMap};

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::Span;

use crate::chc;

use super::body::DefBody;
use super::constraints::Provenance;
use super::file_name;

/// A part of the system solved on its own.
pub struct Part {
    /// Its number among the parts.
    pub id: usize,
    pub clauses: usize,
    /// The functions its clauses come from, in the order of their code.
    pub functions: Vec<PartCode>,
    /// See [`verdict`].
    pub verdict: &'static str,
    /// Whether the verdict was that of an earlier run (`THRUST_CACHE_DIR`).
    pub cached: bool,
}

/// `sat`, `unsat`, `timeout`, `unknown` or `error`.
pub fn verdict(result: &Result<(), chc::CheckSatError>) -> &'static str {
    match result {
        Ok(()) => "sat",
        Err(chc::CheckSatError::Unsat) => "unsat",
        Err(chc::CheckSatError::Timeout(_)) => "timeout",
        Err(chc::CheckSatError::Unknown { .. }) => "unknown",
        Err(_) => "error",
    }
}

/// The verdict of the crate from those of its parts: `unsat` if a part is, else the first that
/// is not `sat`.
pub fn crate_verdict(parts: &[Part]) -> &'static str {
    let mut verdicts = parts.iter().map(|p| p.verdict);
    let unsat = verdicts.clone().any(|v| v == "unsat");
    match unsat {
        true => "unsat",
        false => verdicts.find(|v| *v != "sat").unwrap_or("sat"),
    }
}

/// A function some clauses of a part come from, and the lines they were made at.
#[derive(serde::Serialize)]
pub struct PartCode {
    pub r#fn: String,
    /// `file:first-last`, or `file:line`.
    pub lines: String,
}

impl Part {
    pub fn new(tcx: TyCtxt<'_>, system: &chc::System, id: usize, part: &chc::Part) -> Self {
        Part {
            id,
            clauses: part.clauses.len(),
            functions: code(tcx, system, &part.clauses),
            verdict: verdict(&part.result),
            cached: part.cached,
        }
    }

    /// `` `f` (a.rs:3-6), `g` (a.rs:9-9) ``.
    fn functions(&self) -> String {
        if self.functions.is_empty() {
            return "no function".to_owned();
        }
        let named: Vec<String> = self
            .functions
            .iter()
            .map(|f| format!("`{}` ({})", f.r#fn, f.lines))
            .collect();
        named.join(", ")
    }

    /// What the error of a part that fails says of it.
    pub fn error_note(&self, parts: usize) -> String {
        format!(
            "in part {} of {parts}, of {} clauses from {}",
            self.id,
            self.clauses,
            self.functions()
        )
    }
}

/// Where the clause was made: its function and the span of the code.
fn made_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    bodies: &mut HashMap<LocalDefId, Option<DefBody<'tcx>>>,
    clause: &chc::Clause,
) -> Option<(LocalDefId, Span)> {
    let provenance = Provenance::of(&clause.debug_info);
    let def = provenance.def?;
    let body = bodies.entry(def).or_insert_with(|| {
        tcx.is_mir_available(def.to_def_id())
            .then(|| DefBody::new(tcx, def))
    });
    let in_body = body
        .as_ref()
        .zip(provenance.bb)
        .and_then(|(body, bb)| body.span(bb, provenance.stmt));
    let span = in_body.unwrap_or_else(|| tcx.def_span(def.to_def_id()).source_callsite());
    Some((def, span))
}

/// The functions the clauses `ids` come from, each with the lines its clauses were made at.
fn code(tcx: TyCtxt<'_>, system: &chc::System, ids: &[chc::ClauseId]) -> Vec<PartCode> {
    let mut bodies = HashMap::new();
    let mut lines: BTreeMap<String, (String, usize, usize)> = BTreeMap::new();
    for &id in ids {
        let Some((def, span)) = made_at(tcx, &mut bodies, &system.clauses[id]) else {
            continue;
        };
        let source_map = tcx.sess.source_map();
        let (lo, hi) = (
            source_map.lookup_char_pos(span.lo()),
            source_map.lookup_char_pos(span.hi()),
        );
        let entry = lines
            .entry(tcx.def_path_str(def.to_def_id()))
            .or_insert_with(|| (file_name(tcx, span), lo.line, hi.line));
        entry.1 = entry.1.min(lo.line);
        entry.2 = entry.2.max(hi.line);
    }
    let mut code: Vec<(usize, PartCode)> = lines
        .into_iter()
        .map(|(name, (file, first, last))| {
            let code = PartCode {
                r#fn: name,
                lines: match last > first {
                    true => format!("{file}:{first}-{last}"),
                    false => format!("{file}:{first}"),
                },
            };
            (first, code)
        })
        .collect();
    code.sort_by_key(|(first, _)| *first);
    code.into_iter().map(|(_, code)| code).collect()
}

/// The notes after the errors of the parts: how many were solved and which of them now, and the
/// functions of a failing part whose clauses fall into more than one part, with why.
pub fn emit_notes(tcx: TyCtxt<'_>, parts: &[Part]) {
    let cached = parts.iter().filter(|p| p.cached).count();
    let solved: Vec<String> = parts
        .iter()
        .filter(|p| !p.cached)
        .map(|p| format!("part {} from {}", p.id, p.functions()))
        .collect();
    let mut note = match parts.len() {
        1 if cached == 1 => "thrust: 1 part solved on its own, from an earlier run".to_owned(),
        1 => "thrust: 1 part solved on its own".to_owned(),
        n => format!("thrust: {n} parts solved on their own, {cached} of them from earlier runs"),
    };
    if !solved.is_empty() && cached > 0 {
        note.push_str(&format!("; solved now: {}", solved.join("; ")));
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
