//! What the analysis did with the body of each function of the crate, as it recorded it
//! ([`crate::analyze::BodyChecks`]): checked, and in which query or parts, or why not. A body is
//! verified only when it was checked and the queries holding its clauses are `sat`.

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::Span;

use crate::analyze::BodyCheck;

use super::{parts, Config, Input};

/// A function of the crate, with what the analysis did with its body.
pub struct Function {
    pub name: String,
    /// The whole function.
    pub span: Span,
    /// Its signature, where the human report places it.
    pub head: Span,
    pub check: BodyCheck,
    /// Of a checked body with `THRUST_SPLIT`, the parts its clauses are in, by number.
    pub parts: Option<Vec<usize>>,
    /// Of a checked body, the verdict of the query or of the parts its clauses are in.
    pub verdict: Option<&'static str>,
}

/// Each function of the crate the report shows, but the specification functions, in the order
/// of their code. `verdict` is the whole query's, without `THRUST_SPLIT`.
pub fn functions(
    tcx: TyCtxt<'_>,
    config: &Config,
    input: &Input<'_>,
    verdict: &'static str,
) -> Vec<Function> {
    let mut functions: Vec<Function> = tcx
        .mir_keys(())
        .iter()
        .copied()
        .filter(|def| tcx.def_kind(*def).is_fn_like() && config.reports(tcx, *def))
        .filter_map(|def| {
            let check = input
                .body_checks
                .get(&def)
                .copied()
                .unwrap_or(BodyCheck::NotAnalyzed("not reached by the analysis"));
            if check == BodyCheck::Specification {
                return None;
            }
            Some(function(tcx, input, def, check, verdict))
        })
        .collect();
    functions.sort_by_key(|f| f.span.lo());
    functions
}

fn function(
    tcx: TyCtxt<'_>,
    input: &Input<'_>,
    def: LocalDefId,
    check: BodyCheck,
    verdict: &'static str,
) -> Function {
    let checked = check == BodyCheck::Checked;
    let split = !input.parts.is_empty();
    let in_parts: Vec<&parts::Part> = input
        .parts
        .iter()
        .filter(|p| p.functions.iter().any(|f| f.def == def))
        .collect();
    let verdict = match split {
        true => {
            let verdicts: Vec<&'static str> = in_parts.iter().map(|p| p.verdict).collect();
            parts::crate_verdict(&verdicts)
        }
        false => verdict,
    };
    Function {
        name: tcx.def_path_str(def.to_def_id()),
        span: tcx
            .hir_span_with_body(tcx.local_def_id_to_hir_id(def))
            .source_callsite(),
        head: tcx.def_span(def.to_def_id()).source_callsite(),
        check,
        parts: (checked && split).then(|| in_parts.iter().map(|p| p.id).collect()),
        verdict: checked.then_some(verdict),
    }
}

impl Function {
    /// `checked, in part 2 (sat)`, `trusted: #[thrust::trusted]`.
    pub fn describe(&self) -> String {
        let status = self.check.status().replace('_', " ");
        if let Some(reason) = self.check.reason() {
            return format!("{status}: {reason}");
        }
        let verdict = self.verdict.unwrap_or_default();
        match self.parts.as_deref() {
            None => format!("{status} ({verdict})"),
            Some([]) => format!("{status}, with no clause ({verdict})"),
            Some([part]) => format!("{status}, in part {part} ({verdict})"),
            Some(parts) => {
                let parts: Vec<String> = parts.iter().map(usize::to_string).collect();
                format!("{status}, in parts {} ({verdict})", parts.join(", "))
            }
        }
    }
}

/// `4 functions: 2 checked, 1 trusted, 1 ignored`.
pub fn summary(functions: &[Function]) -> String {
    let mut counts: Vec<(&'static str, usize)> = Vec::new();
    for f in functions {
        match counts
            .iter_mut()
            .find(|(status, _)| *status == f.check.status())
        {
            Some((_, n)) => *n += 1,
            None => counts.push((f.check.status(), 1)),
        }
    }
    counts.sort_by_key(|(status, _)| STATUSES.iter().position(|s| s == status));
    let counts: Vec<String> = counts
        .iter()
        .map(|(status, n)| format!("{n} {}", status.replace('_', " ")))
        .collect();
    let noun = if functions.len() == 1 {
        "function"
    } else {
        "functions"
    };
    format!("{} {noun}: {}", functions.len(), counts.join(", "))
}

const STATUSES: [&str; 5] = [
    "checked",
    "trusted",
    "ignored",
    "unselected",
    "not_analyzed",
];
