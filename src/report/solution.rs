//! The solver's model applied to the templates: the interpretation of each predicate variable,
//! and each template with its predicate variables replaced by theirs.

use std::collections::HashMap;

use crate::chc;

use super::expr::Expr;
use super::model::{self, Interpretation};
use super::sites::{Names, Site, SiteParam};

/// The solver's interpretation of each predicate variable, by its name in the report.
pub(super) struct Solution {
    by_name: HashMap<String, Interpretation>,
}

impl Solution {
    /// The interpretations of `model`, simplified by `z3`, which `run` runs (see
    /// [`super::simplify`]).
    pub(super) fn new(
        model: &str,
        query: &str,
        names: &Names,
        run: impl Fn(&str) -> Option<String>,
    ) -> Self {
        let mut model = model::read(model);
        // `z3`'s model of a system of clauses interprets the predicate variables by formulas over
        // their arguments; a function it made up besides would need its definition shown.
        if let Some(name) = model.keys().find(|name| !names.is_pred_var(name)) {
            unimplemented!("a model defining `{name}`, which is no predicate variable");
        }
        // Only the predicate variables the report names are shown.
        let named: std::collections::HashSet<String> =
            names.preds.keys().map(|p| p.to_string()).collect();
        model.retain(|name, _| named.contains(name));
        super::simplify::simplify(&mut model, query, run);
        // An interpretation takes the arguments in the order they are shown.
        let by_name = names
            .preds
            .iter()
            .filter_map(|(p, info)| {
                let interpretation = model.get(&p.to_string())?;
                let params = names.pred_head(*p).arrange(&interpretation.params);
                let arranged = Interpretation {
                    params,
                    body: interpretation.body.clone(),
                    source: None,
                };
                Some((info.name.clone(), arranged))
            })
            .collect();
        Solution { by_name }
    }

    /// `e` with each predicate variable replaced by its interpretation.
    pub(super) fn apply(&self, e: &Expr) -> Expr {
        match e {
            Expr::Sym(_) => e.clone(),
            Expr::App(f, args) => {
                let args: Vec<Expr> = args.iter().map(|a| self.apply(a)).collect();
                match self.by_name.get(f) {
                    Some(interpretation) => interpretation.apply(&args),
                    None => Expr::App(f.clone(), args),
                }
            }
            Expr::Quant(q, vars, body) => Expr::Quant(q, vars.clone(), Box::new(self.apply(body))),
            Expr::Pred(p, groups, args) => {
                let args: Vec<Expr> = args.iter().map(|a| self.apply(a)).collect();
                match self.by_name.get(p) {
                    Some(interpretation) => interpretation.apply(&args),
                    None => Expr::Pred(p.clone(), groups.clone(), args),
                }
            }
        }
    }

    /// `name(args) := body` for each predicate variable of `site`.
    pub(super) fn lines(&self, site: &Site, names: &Names) -> Vec<String> {
        site.preds
            .iter()
            .filter_map(|p| names.preds.get(p))
            .map(|info| {
                let unique =
                    |a: &String| info.args.iter().filter(|b| b.as_ref() == Some(a)).count() == 1;
                let args: Vec<String> = info
                    .args
                    .iter()
                    .enumerate()
                    .map(|(k, a)| match a {
                        Some(a) if unique(a) => a.clone(),
                        _ => format!("x{k}"),
                    })
                    .collect();
                let args: Vec<Expr> = args.into_iter().map(Expr::sym).collect();
                let head = Expr::Pred(info.name.clone(), info.groups.clone(), args.clone());
                match self.by_name.get(&info.name) {
                    Some(interpretation) => format!("{head} := {}", interpretation.apply(&args)),
                    None => format!("{head}: not in the query"),
                }
            })
            .collect()
    }
}

/// Why there is no solution to show, if there is none.
pub(super) fn solution_unavailable(answer: &chc::Answer) -> Option<String> {
    use chc::CheckSatError;
    let why = match &answer.result {
        Ok(()) => None,
        Err(CheckSatError::Unsat) => Some("the constraints have none (see `failure`)".to_owned()),
        Err(CheckSatError::Timeout(limit)) => {
            Some(format!("the solver did not answer within {limit:?}"))
        }
        Err(CheckSatError::Unknown { .. }) => Some("the solver answered unknown".to_owned()),
        Err(CheckSatError::UnsoundSat { .. }) => Some(
            "the solver answered sat only after rejecting part of the query it does not support"
                .to_owned(),
        ),
        Err(
            CheckSatError::NoVerdict { .. } | CheckSatError::Error { .. } | CheckSatError::Io(_),
        ) => Some("the solver gave no answer (see the verification error)".to_owned()),
    };
    if let Some(why) = why {
        return Some(format!("no solution: {why}"));
    }
    if chc::pred_args_rewritten() {
        return Some(
            "no solution shown: `THRUST_FLAT_PRED_ARGS` or `THRUST_DEDUP_PRED_ARGS` rewrites the \
             arguments the solver interprets"
                .to_owned(),
        );
    }
    if answer.model.is_none() {
        return Some(
            "no solution: the solver gave no model (only `z3` is asked for one)".to_owned(),
        );
    }
    None
}

pub(super) fn refined(param: &SiteParam, refinement: &Expr) -> String {
    if refinement.is_true() {
        return param.ty.clone();
    }
    format!("{{{} | {refinement}}}", param.ty)
}

/// The template of a contract site as a signature, each refinement passed through `f`.
pub(super) fn signature(name: &str, site: &Site, f: &impl Fn(&Expr) -> Expr) -> String {
    let (ret, params) = site.params.split_last().unwrap();
    let params: Vec<String> = params
        .iter()
        .map(|p| format!("{}: {}", p.name, refined(p, &f(&p.refinement))))
        .collect();
    format!(
        "fn {name}({}) -> {}",
        params.join(", "),
        refined(ret, &f(&ret.refinement))
    )
}

/// The template of a block site as one formula over its variables, passed through `f`.
pub(super) fn invariant(site: &Site, f: &impl Fn(&Expr) -> Expr) -> Expr {
    Expr::and(site.params.iter().map(|p| f(&p.refinement)).collect())
}

/// The template of a block site: the signature of the predicate variable that is the whole of it,
/// `main.loop#1(x: i64, y: i64)`, or else a closure over its variables, as `invariant!` takes it.
pub(super) fn block_template(site: &Site, names: &Names) -> String {
    match site.signature {
        Some(p) => format!("{}({})", names.pred_head(p).name, over(site)),
        None => format!("|{}| {}", over(site), invariant(site, &|e| e.clone())),
    }
}

pub(super) fn over(site: &Site) -> String {
    let vars: Vec<String> = site
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty))
        .collect();
    vars.join(", ")
}

/// The written form of an inferred contract.
pub(super) fn contract_help(site: &Site, solution: &Solution) -> Option<String> {
    let (ret, params) = site.params.split_last().unwrap();
    let requires = Expr::and(
        params
            .iter()
            .map(|p| solution.apply(&p.refinement))
            .collect(),
    );
    let ensures = solution.apply(&ret.refinement);
    let mut attrs = Vec::new();
    if !requires.is_true() {
        attrs.push(format!("#[thrust_macros::requires({requires})]"));
    }
    if !ensures.is_true() {
        attrs.push(format!("#[thrust_macros::ensures({ensures})]"));
    }
    (!attrs.is_empty()).then(|| format!("as a contract: {}", attrs.join(" ")))
}
