//! Derived predicates: a trait's `#[thrust_macros::predicate(derived)]` at an impl that leaves
//! it undefined.
//!
//! Such a predicate `P` is declared as an unknown. Its rules are the clauses that check the
//! `ensures` of the impl's own functions and laws (and an impl method's own contract against the
//! trait's), and its meaning is their least model, as a loop invariant's is that of the loop's
//! entry and back edge. The meaning holds under two conditions on the clause system, with the
//! other unknowns fixed at a solution's values:
//!
//! - every clause that concludes `P` (where `P` occurs positively in `¬body ∨ head`) is a rule,
//!   and definite in `P`: then the rules have a least model `μ`, contained in every solution
//!   (the least model of constrained Horn clauses, `bjorner2015horn` Proposition 3; with bodies
//!   monotone in `P`, the least fixed point of a monotone operator, by Knaster and Tarski);
//! - every other clause has `P` only negatively, that is assumed: such a clause is antitone in
//!   `P`, so it stays valid when a solution's `P` shrinks to `μ`.
//!
//! The system then has a solution exactly when it has one with `P := μ`, so a verdict means what
//! it would with `μ` written as the body. [`check`] reports every clause that breaks either
//! condition, and an impl function whose body is not analyzed, which gives no rule although its
//! contract is assumed.

use std::collections::{HashMap, HashSet};

use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeVisitableExt as _};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze::{BodyCheck, BodyChecks};
use crate::chc;
use crate::report::constraints::Provenance;
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
    /// laws are analyzed when it has no function).
    fn is_rule_site(&self, tcx: TyCtxt<'tcx>, site: DefId) -> bool {
        site == self.impl_def_id || tcx.impl_of_assoc(site) == Some(self.impl_def_id)
    }
}

/// Whether a clause is a rule of a derived predicate declared at `at`: it checks the `ensures`
/// of a function of the impl at its return (an inherited law's under the impl), or relates an
/// impl method's own contract to the trait's.
fn is_rule<'tcx>(tcx: TyCtxt<'tcx>, clause: &chc::Clause, at: &DerivedAt<'tcx>) -> bool {
    let provenance = Provenance::of(&clause.debug_info);
    let Some(site) = provenance.owner.or(provenance.def) else {
        return false;
    };
    let checks_ensures = clause.debug_info.get("term") == Some("return")
        || clause.debug_info.get("span") == Some("impl_refinement");
    checks_ensures && at.is_rule_site(tcx, site.to_def_id())
}

/// The span to report a clause at: the code it was made at, or else the impl.
fn clause_span<'tcx>(
    tcx: TyCtxt<'tcx>,
    clause: &chc::Clause,
    at: &DerivedAt<'tcx>,
) -> rustc_span::Span {
    Provenance::of(&clause.debug_info)
        .span(tcx)
        .unwrap_or_else(|| tcx.def_span(at.impl_def_id))
}

/// Reports what breaks the conditions of the module documentation for the derived predicates
/// `derived` (symbol to where it is declared), and stops if anything does.
pub fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    system: &chc::System,
    derived: &HashMap<chc::UserDefinedPred, DerivedAt<'tcx>>,
    contracts: &[(LocalDefId, rty::FunctionType)],
    body_checks: &BodyChecks,
) {
    for at in derived.values() {
        check_rule_sites_analyzed(tcx, at, body_checks);
    }
    for (pred, at) in derived {
        check_unproven_assumptions(tcx, system, pred, at, contracts, body_checks);
    }
    let preds: HashSet<&chc::UserDefinedPred> = derived.keys().collect();
    let mut reported = HashSet::new();
    for (id, pred, definite) in system.conclusions_of(&preds) {
        let at = &derived[pred];
        let clause = &system.clauses[id];
        let message = if !is_rule(tcx, clause, at) {
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
        tracing::debug!(?id, debug_info = %clause.debug_info.display(""), "{message}");
        let span = clause_span(tcx, clause, at);
        if reported.insert((span, pred.clone())) {
            tcx.dcx().span_err(span, message);
        }
    }
    tcx.dcx().abort_if_errors();
}

/// Reports each function of the impl at `at` whose body is not analyzed: its contract is assumed
/// where it is called, but it gives the derived predicate no rule.
fn check_rule_sites_analyzed<'tcx>(
    tcx: TyCtxt<'tcx>,
    at: &DerivedAt<'tcx>,
    body_checks: &BodyChecks,
) {
    for &item in tcx.associated_item_def_ids(at.impl_def_id) {
        let Some(check) = item.as_local().and_then(|local| body_checks.get(local)) else {
            continue;
        };
        if matches!(check, BodyCheck::Checked | BodyCheck::Specification) {
            continue;
        }
        tcx.dcx().span_err(
            tcx.def_span(item),
            format!(
                "`{}` is {} here, so its body gives no rule of the derived predicate `{}`, whose \
                 meaning is the least relation its impl's bodies derive; analyze it or define the \
                 predicate in the impl",
                tcx.item_name(item),
                check.status(),
                at.path(tcx)
            ),
        );
    }
}

/// Reports each concrete contract that assumes `pred` negatively (negated, or in a premise)
/// without the assumption being proven in the system: a function's own `requires`, which its
/// body assumes and only the crate's callers establish, and the `ensures` of a function whose
/// body is not analyzed. Such an assumption is weaker of the least relation than of a larger
/// one, so a solution with a larger relation could rely on more than the contract states of the
/// least. An assumption proven in the system (an analyzed callee's `ensures`, a generic
/// function's contract, verified for every interpretation of the trait's predicates) may take
/// either polarity, and is left alone.
fn check_unproven_assumptions<'tcx>(
    tcx: TyCtxt<'tcx>,
    system: &chc::System,
    pred: &chc::UserDefinedPred,
    at: &DerivedAt<'tcx>,
    contracts: &[(LocalDefId, rty::FunctionType)],
    body_checks: &BodyChecks,
) {
    for (def, fn_ty) in contracts {
        let args: Vec<chc::Term> = (0..fn_ty.params.len())
            .map(|i| chc::Term::Var(chc::TermVarIdx::from_usize(i)))
            .collect();
        let result = chc::Term::Var(chc::TermVarIdx::from_usize(args.len()));
        let unanalyzed = body_checks
            .get(*def)
            .is_some_and(|check| !matches!(check, BodyCheck::Checked | BodyCheck::Specification));
        let what = if system.occurs_negatively(&fn_ty.precondition_formula(&args), pred) {
            "precondition"
        } else if unanalyzed
            && system.occurs_negatively(&fn_ty.postcondition_formula(&args, result), pred)
        {
            "postcondition, assumed without its body analyzed,"
        } else {
            continue;
        };
        tcx.dcx().span_err(
            tcx.def_span(*def),
            format!(
                "the {what} of `{}` assumes the derived predicate `{}` negated or in a premise, \
                 which a larger relation than the least one could make stronger than stated; \
                 define the predicate in the impl",
                tcx.def_path_str(*def),
                at.path(tcx)
            ),
        );
    }
}
