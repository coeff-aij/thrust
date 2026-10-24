//! Derived predicates: a trait's `#[thrust_macros::predicate(derived)]` at an impl that leaves
//! it undefined.
//!
//! Such a predicate `P` is declared as an unknown, and its meaning is the least relation its
//! rules derive, as a loop invariant's is that of the loop's entry and back edge. With the other
//! unknowns fixed at a solution's values, a verdict reads as with that relation written when:
//!
//! - R: the clauses that check `P` positively are its rules, the checks of the `ensures` of the
//!   impl's functions and of the trait's laws it inherits, each definite in `P`; and every one of
//!   them is analyzed. Then the rules have a least model, contained in every solution
//!   (`bjorner2015horn` Proposition 3; for bodies monotone beyond conjunctions of atoms, the
//!   least fixed point of a monotone operator, `tarski1955lattice`).
//! - C: every other check has `P` only negatively, so what it proves of a solution's `P` holds of
//!   the least relation.
//! - A: every assumption the system does not discharge has `P` only positively, so a statement
//!   true of the least relation stays true of a solution's.
//!
//! The marks this needs are set where the clauses and assumptions are made, not read back from
//! debug information: [`Evidence`] records which clauses check whose `ensures`, which inherited
//! laws were checked for which impl, and every contract assumed (a body's own precondition, and
//! the postcondition at each call with what it resolves to). An assumption counts as discharged
//! only when it is the postcondition of a call that resolves to a body the crate analyzes; every
//! other one (a trusted function, generic or a trait's default method included, an extern
//! specification, `std.rs`, a function outside `THRUST_VERIFY_ONLY`, a call through a value) gets
//! condition A at the instance it is assumed at.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeVisitableExt as _};
use rustc_span::def_id::DefId;
use rustc_span::Span;

use crate::analyze::{BodyCheck, BodyChecks};
use crate::chc;
use crate::chc::debug::Provenance;
use crate::rty;

/// Where a derived predicate is declared: the trait item `pred_def_id` at the impl
/// `impl_def_id`.
#[derive(Debug, Clone, Copy)]
pub struct DerivedAt<'tcx> {
    pub pred_def_id: DefId,
    pub impl_def_id: DefId,
    pub trait_ref: mir_ty::TraitRef<'tcx>,
}

impl<'tcx> DerivedAt<'tcx> {
    /// The impl of `pred_def_id`'s trait at the trait arguments of `generic_args`, when one impl
    /// of the crate is for exactly those arguments: `None` for an instance of a generic impl.
    pub fn new(
        tcx: TyCtxt<'tcx>,
        pred_def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<Self> {
        let trait_def_id = tcx.trait_of_assoc(pred_def_id)?;
        let trait_args = generic_args.truncate_to(tcx, tcx.generics_of(trait_def_id));
        let trait_ref = tcx.erase_regions(mir_ty::TraitRef::new(tcx, trait_def_id, trait_args));
        let impl_def_id = tcx.all_impls(trait_def_id).find(|impl_def_id| {
            let impl_ref = tcx.impl_trait_ref(*impl_def_id).unwrap();
            let impl_ref = tcx.erase_regions(impl_ref.instantiate_identity());
            !impl_ref.has_param() && impl_ref == trait_ref
        })?;
        Some(Self {
            pred_def_id,
            impl_def_id,
            trait_ref,
        })
    }

    /// The predicate as a path, `<Range as Iter>::produces`.
    fn path(&self, tcx: TyCtxt<'tcx>) -> String {
        format!("{}::{}", self.trait_ref, tcx.item_name(self.pred_def_id))
    }

    /// Whether `site` is a function of the impl, or the impl itself (under which its inherited
    /// laws are checked when it has no function).
    fn is_rule_site(&self, tcx: TyCtxt<'tcx>, site: DefId) -> bool {
        site == self.impl_def_id || tcx.impl_of_assoc(site) == Some(self.impl_def_id)
    }
}

/// A contract assumed by the analysis.
#[derive(Debug, Clone)]
pub enum Assumption<'tcx> {
    /// A body's own precondition, which the system proves only at this crate's calls.
    OwnRequires,
    /// The postcondition after a call, to the function and arguments given when the callee is a
    /// constant (`None` for a call through a value).
    CallEnsures(Option<(DefId, mir_ty::GenericArgsRef<'tcx>)>),
}

/// The marks the conditions of the module documentation are checked against, set where the
/// analysis makes the clauses and the assumptions.
#[derive(Debug, Default)]
pub struct Evidence<'tcx> {
    /// The clauses that check a function's `ensures`, by the function (for a trait's default law
    /// checked for an impl, the impl's function or the impl).
    ensures_checks: HashMap<chc::ClauseId, DefId>,
    /// Each inherited law checked, with the impl it was checked for.
    inherited_laws: HashSet<(DefId, DefId)>,
    assumptions: Vec<(Assumption<'tcx>, Span, rty::FunctionType)>,
}

impl<'tcx> Evidence<'tcx> {
    /// Marks the clauses with indices in `clauses` as checks of the `ensures` of `site`.
    pub fn ensures_checked(&mut self, clauses: Range<usize>, site: DefId) {
        for idx in clauses {
            self.ensures_checks
                .insert(chc::ClauseId::from_usize(idx), site);
        }
    }

    pub fn inherited_law_checked(&mut self, impl_def_id: DefId, law: DefId) {
        self.inherited_laws.insert((impl_def_id, law));
    }

    pub fn assume(
        &mut self,
        assumption: Assumption<'tcx>,
        span: Span,
        contract: rty::FunctionType,
    ) {
        self.assumptions.push((assumption, span, contract));
    }
}

/// Whether the system discharges an assumption: the postcondition of a call that resolves to a
/// body the crate analyzes. A missing record counts as not analyzed.
fn is_discharged<'tcx>(
    tcx: TyCtxt<'tcx>,
    assumption: &Assumption<'tcx>,
    body_checks: &BodyChecks,
) -> bool {
    let Assumption::CallEnsures(Some((def_id, args))) = assumption else {
        return false;
    };
    let resolved = if args.has_param() {
        *def_id
    } else {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        mir_ty::Instance::try_resolve(tcx, typing_env, *def_id, args)
            .ok()
            .flatten()
            .map_or(*def_id, |instance| instance.def_id())
    };
    resolved
        .as_local()
        .and_then(|local| body_checks.get(local))
        .is_some_and(|check| check == BodyCheck::Checked)
}

/// Reports what breaks the conditions of the module documentation for the derived predicates
/// `derived` (symbol to where it is declared), and stops if anything does.
pub fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    system: &chc::System,
    derived: &HashMap<chc::UserDefinedPred, DerivedAt<'tcx>>,
    evidence: &Evidence<'tcx>,
    body_checks: &BodyChecks,
    trait_laws: &rustc_data_structures::fx::FxIndexMap<DefId, Vec<DefId>>,
) {
    for at in derived.values() {
        check_rule_sites_analyzed(tcx, at, evidence, body_checks, trait_laws);
    }
    let preds: HashSet<&chc::UserDefinedPred> = derived.keys().collect();
    check_assumptions(tcx, system, derived, &preds, evidence, body_checks);
    check_conclusions(tcx, system, derived, &preds, evidence);
    tcx.dcx().abort_if_errors();
}

/// Condition R's analyzed sites: every function of the impl, and every law of the trait it
/// inherits, checked for it.
fn check_rule_sites_analyzed<'tcx>(
    tcx: TyCtxt<'tcx>,
    at: &DerivedAt<'tcx>,
    evidence: &Evidence<'tcx>,
    body_checks: &BodyChecks,
    trait_laws: &rustc_data_structures::fx::FxIndexMap<DefId, Vec<DefId>>,
) {
    let unanalyzed = |item: DefId, status: &str| {
        tcx.dcx().span_err(
            tcx.def_span(item),
            format!(
                "`{}` is {status} for `{}`, so it gives no rule of the derived predicate `{}`, \
                 whose meaning is the least relation its impl's bodies derive; analyze it or \
                 define the predicate in the impl",
                tcx.item_name(item),
                at.trait_ref.self_ty(),
                at.path(tcx)
            ),
        );
    };
    for &item in tcx.associated_item_def_ids(at.impl_def_id) {
        if !tcx.def_kind(item).is_fn_like() {
            continue;
        }
        let check = item.as_local().and_then(|local| body_checks.get(local));
        match check {
            Some(BodyCheck::Checked | BodyCheck::Specification) => {}
            Some(check) => unanalyzed(item, check.status()),
            None => unanalyzed(item, "not analyzed"),
        }
    }
    let implemented = tcx.impl_item_implementor_ids(at.impl_def_id);
    let laws = trait_laws.get(&at.trait_ref.def_id).into_iter().flatten();
    for &law in laws {
        let inherited = !implemented.contains_key(&law);
        if inherited && !evidence.inherited_laws.contains(&(at.impl_def_id, law)) {
            unanalyzed(law, "not checked");
        }
    }
}

/// Condition A: each assumption the system does not discharge has the derived predicates only
/// positively, at the instance it is assumed at.
fn check_assumptions<'tcx>(
    tcx: TyCtxt<'tcx>,
    system: &chc::System,
    derived: &HashMap<chc::UserDefinedPred, DerivedAt<'tcx>>,
    preds: &HashSet<&chc::UserDefinedPred>,
    evidence: &Evidence<'tcx>,
    body_checks: &BodyChecks,
) {
    let mut assumed = Vec::new();
    for (assumption, span, contract) in &evidence.assumptions {
        if is_discharged(tcx, assumption, body_checks) {
            continue;
        }
        let args: Vec<chc::Term> = (0..contract.params.len())
            .map(|i| chc::Term::Var(chc::TermVarIdx::from_usize(i)))
            .collect();
        let formula = match assumption {
            Assumption::OwnRequires => contract.precondition_formula(&args),
            Assumption::CallEnsures(_) => {
                let result = chc::Term::Var(chc::TermVarIdx::from_usize(args.len()));
                contract.postcondition_formula(&args, result)
            }
        };
        assumed.push((assumption, *span, formula));
    }
    let formulas: Vec<&chc::Formula> = assumed.iter().map(|(_, _, f)| f).collect();
    let mut reported = HashSet::new();
    for (idx, pred) in system.negative_occurrences(&formulas, preds) {
        let (assumption, span, _) = &assumed[idx];
        if !reported.insert((*span, pred.clone())) {
            continue;
        }
        let what = match assumption {
            Assumption::OwnRequires => {
                "this function's own precondition, which only this \
                                        crate's callers establish,"
            }
            Assumption::CallEnsures(_) => {
                "the postcondition of this call, whose callee's body \
                                           is not analyzed,"
            }
        };
        tcx.dcx().span_err(
            *span,
            format!(
                "{what} assumes the derived predicate `{}` negated or in a premise, which a \
                 larger relation than the least one could make stronger than stated; define the \
                 predicate in the impl",
                derived[pred].path(tcx)
            ),
        );
    }
}

/// Conditions R (definite rules) and C (no other check concludes a derived predicate).
fn check_conclusions<'tcx>(
    tcx: TyCtxt<'tcx>,
    system: &chc::System,
    derived: &HashMap<chc::UserDefinedPred, DerivedAt<'tcx>>,
    preds: &HashSet<&chc::UserDefinedPred>,
    evidence: &Evidence<'tcx>,
) {
    let mut reported = HashSet::new();
    for (id, pred, definite) in system.conclusions_of(preds) {
        let at = &derived[pred];
        let is_rule = evidence
            .ensures_checks
            .get(&id)
            .is_some_and(|site| at.is_rule_site(tcx, *site));
        let message = if !is_rule {
            format!(
                "the derived predicate `{}` is concluded here, outside the `ensures` of its \
                 impl's functions and laws, which would add a fact its rules do not derive; \
                 define it in the impl",
                at.path(tcx)
            )
        } else if !definite {
            format!(
                "this `ensures` concludes the derived predicate `{}` in a disjunction, under an \
                 existential or in a premise, so its rules have no least relation; define it in \
                 the impl",
                at.path(tcx)
            )
        } else {
            continue;
        };
        let clause = &system.clauses[id];
        let span = Provenance::of(&clause.debug_info)
            .span(tcx)
            .unwrap_or_else(|| tcx.def_span(at.impl_def_id));
        if reported.insert((span, pred.clone())) {
            tcx.dcx().span_err(span, message);
        }
    }
}
