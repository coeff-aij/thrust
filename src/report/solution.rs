//! The solver's model applied to the templates: the interpretation of each predicate variable,
//! and each template with its predicate variables replaced by theirs.

use std::collections::HashMap;

use crate::chc;

use super::formula::{self, map_atoms, show, Formula, Name, Term};
use crate::chc::answer::{self, Symbols};
use crate::chc::sexp::Sexp;

use super::sites::{Names, Site, SiteParam};

/// The solver's interpretation of a predicate variable.
pub(super) type Interpretation = answer::Definition<Name>;

/// The solver's interpretation of each predicate variable the report names.
pub(super) struct Solution {
    by_pred: HashMap<chc::PredVarId, Interpretation>,
    /// Whether it is that of some parts of the system only (`THRUST_SPLIT`).
    partial: bool,
}

/// Why a site of a part without a solution has none.
pub(super) const UNSOLVED_PART: &str = "no solution: the part of the constraints over it has none";

impl Solution {
    /// The interpretations of `model`, simplified by `z3`, which `run` runs (see
    /// [`super::simplify`]).
    pub(super) fn new(
        model: &Sexp,
        query: &str,
        symbols: &Symbols,
        names: &Names,
        run: impl Fn(&str) -> Option<String>,
    ) -> Self {
        let mut model = answer::definitions(model, symbols, Name::new);
        // `z3`'s model of a system of clauses interprets the predicate variables by formulas over
        // their arguments; a function it made up besides would need its definition shown.
        if let Some(name) = model.keys().find(|name| symbols.pred(name).is_none()) {
            unimplemented!("a model defining `{name}`, which is no predicate variable");
        }
        // Only the predicate variables the report names are shown.
        model.retain(|name, _| names.preds.contains_key(&symbols.pred(name).unwrap()));
        super::simplify::simplify(&mut model, query, symbols, run);
        let by_pred = model
            .into_iter()
            .map(|(name, interpretation)| (symbols.pred(&name).unwrap(), interpretation))
            .collect();
        Solution {
            by_pred,
            partial: false,
        }
    }

    /// The solution of the parts each of `answers` solved, from those with a model, `partial` when
    /// they are parts of the system (`THRUST_SPLIT`); or why there is none, from the first.
    pub(super) fn of_parts(
        answers: &[chc::Answer],
        partial: bool,
        symbols: &Symbols,
        names: &Names,
    ) -> Result<Self, String> {
        let config = chc::Config::from_env();
        let mut solutions = answers.iter().filter_map(|answer| {
            let (None, Some(model)) = (solution_unavailable(answer), &answer.model) else {
                return None;
            };
            let query = answer.query.as_deref().unwrap_or_default();
            Some(Solution::new(model, query, symbols, names, |script| {
                config.run_script(script)
            }))
        });
        let Some(mut solution) = solutions.next() else {
            let why = solution_unavailable(&answers[0]);
            return Err(why.unwrap_or_else(|| "no solution".to_owned()));
        };
        for other in solutions {
            solution.by_pred.extend(other.by_pred);
        }
        solution.partial = partial;
        Ok(solution)
    }

    /// Whether the solution covers `site`: not when it is that of other parts only.
    pub(super) fn solves(&self, site: &Site) -> bool {
        !self.partial || site.preds.iter().any(|p| self.interprets(*p))
    }

    /// Whether the solver interprets `p`: not when the query leaves it out (see
    /// `crate::chc::prune`).
    pub(super) fn interprets(&self, p: chc::PredVarId) -> bool {
        self.by_pred.contains_key(&p)
    }

    /// `f` with each predicate variable replaced by its interpretation.
    pub(super) fn apply(&self, f: &Formula) -> Formula {
        map_atoms(f.clone(), &|atom| {
            let chc::Pred::Var(p) = atom.pred else {
                return atom.into();
            };
            let Some(interpretation) = self.by_pred.get(&p) else {
                return atom.into();
            };
            let applied = interpretation.apply(&atom.args);
            match atom.guard {
                Some(guard) => guard.implies(applied),
                None => applied,
            }
        })
    }

    /// `name args := body` for each predicate variable of `site`.
    pub(super) fn lines(&self, site: &Site, names: &Names) -> Vec<String> {
        site.preds
            .iter()
            .filter_map(|p| Some((*p, names.preds.get(p)?)))
            .map(|(p, info)| {
                let unique =
                    |a: &String| info.args.iter().filter(|b| b.as_ref() == Some(a)).count() == 1;
                let shown: Vec<Term> = info
                    .args
                    .iter()
                    .enumerate()
                    .map(|(k, a)| match a {
                        Some(a) if unique(a) => Term::Var(Name::new(a)),
                        _ => Term::Var(Name::new(&format!("x{k}"))),
                    })
                    .collect();
                let args = names.unarrange(p, shown);
                let head = chc::Atom::new(p.into(), args.clone()).into();
                match self.by_pred.get(&p) {
                    Some(interpretation) => format!(
                        "{} := {}",
                        show(&head, names),
                        show(&interpretation.apply(&args), names)
                    ),
                    None => format!("{}: not in the query", show(&head, names)),
                }
            })
            .collect()
    }
}

/// Why there is no solution to show, if there is none.
pub(super) fn solution_unavailable(answer: &chc::Answer) -> Option<String> {
    // What the solver answered instead is the verification error.
    if answer.result.is_err() {
        return Some("no solution: the solver gave none".to_owned());
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

fn refined(param: &SiteParam, refinement: Formula, names: &Names) -> String {
    let refinement = formula::and(vec![refinement]);
    if refinement.is_top() {
        return param.ty.clone();
    }
    format!("{{{} | {}}}", param.ty, show(&refinement, names))
}

/// The template of a contract site as a signature, each refinement passed through `f`.
pub(super) fn signature(
    name: &str,
    site: &Site,
    names: &Names,
    f: &impl Fn(&Formula) -> Formula,
) -> String {
    let (ret, params) = site.params.split_last().unwrap();
    let params: Vec<String> = params
        .iter()
        .map(|p| format!("{}: {}", p.name, refined(p, f(&p.refinement), names)))
        .collect();
    format!(
        "fn {name}({}) -> {}",
        params.join(", "),
        refined(ret, f(&ret.refinement), names)
    )
}

/// The template of a block site as one formula over its variables, passed through `f`.
pub(super) fn invariant(site: &Site, names: &Names, f: &impl Fn(&Formula) -> Formula) -> String {
    let conjuncts = site.params.iter().map(|p| f(&p.refinement)).collect();
    show(&formula::and(conjuncts), names)
}

/// The template of a block site: the signature of the predicate variable that is the whole of it,
/// `main.loop#1(x: int, y: int)`, or else a closure over its variables, as `invariant!` takes it.
pub(super) fn block_template(site: &Site, names: &Names) -> String {
    match site.signature.and_then(|p| names.preds.get(&p)) {
        Some(info) => format!("{}({})", info.name, over(site)),
        None => format!(
            "|{}| {}",
            over(site),
            invariant(site, names, &Formula::clone)
        ),
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
