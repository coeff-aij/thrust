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
//! - A: every assumption the system does not discharge depends on `P` only monotonically, so a
//!   statement true of the least relation stays true of a solution's. It is checked against the
//!   dependency closure `D` of the derived predicates ([`dependency`] by item,
//!   `chc::dependence` by symbol): walked with its polarity through the bodies known where it is
//!   assumed, an assumption may apply `P` only positively and no other member without a body.
//!
//! The marks this needs are set where the clauses and assumptions are made, not read back from
//! debug information: [`Evidence`] records which clauses check whose `ensures`, which inherited
//! laws were checked for which impl, and every contract assumed (a body's own precondition, and
//! the postcondition at each call with what it resolves to). An assumption counts as discharged
//! only when it is the postcondition of a call that resolves to a body the crate analyzes (for a
//! trait's method called at a type parameter, every impl's); every
//! other one (a trusted function, generic or a trait's default method included, an extern
//! specification, `std.rs`, a function outside `THRUST_VERIFY_ONLY`, a call through a value) gets
//! condition A where it is assumed, over a generic body's type parameters too.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use rustc_hir::def::DefKind;
use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeVisitableExt as _};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::Span;

use crate::analyze::{pred_inst, BodyCheck, BodyChecks};
use crate::chc;
use crate::chc::debug::Provenance;
use crate::chc::dependence::ForallMember;
use crate::rty;

mod dependency;

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
    let analyzed = |def_id: DefId| {
        def_id
            .as_local()
            .and_then(|local| body_checks.get(local))
            .is_some_and(|check| check == BodyCheck::Checked)
    };
    // A call in a generic body names the callee it is written with. A trait's method called at a
    // type parameter reaches, at each instance, the method of one impl, so the call is
    // discharged when every impl's method (or the default it inherits) is analyzed.
    if args.has_param() {
        let Some(trait_def_id) = tcx.trait_of_assoc(*def_id) else {
            return analyzed(*def_id);
        };
        return tcx.all_impls(trait_def_id).all(|impl_def_id| {
            let implementors = tcx.impl_item_implementor_ids(impl_def_id);
            analyzed(implementors.get(def_id).copied().unwrap_or(*def_id))
        });
    }
    // One that does not resolve is not known to reach an analyzed body.
    let resolved = {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let Some(instance) = mir_ty::Instance::try_resolve(tcx, typing_env, *def_id, args)
            .ok()
            .flatten()
        else {
            return false;
        };
        instance.def_id()
    };
    analyzed(resolved)
}

/// Reports what breaks the conditions of the module documentation for the derived predicates
/// `derived` (symbol to where it is declared), and stops if anything does.
pub fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    system: &chc::System,
    derived: &HashMap<chc::UserDefinedPred, DerivedAt<'tcx>>,
    origins: &HashMap<chc::ForallPred, pred_inst::ForallPredOrigin<'tcx>>,
    evidence: &Evidence<'tcx>,
    body_checks: &BodyChecks,
    trait_laws: &rustc_data_structures::fx::FxIndexMap<DefId, Vec<DefId>>,
) {
    for at in derived.values() {
        check_rule_sites_analyzed(tcx, at, evidence, body_checks, trait_laws);
    }
    let preds: HashSet<&chc::UserDefinedPred> = derived.keys().collect();
    check_assumptions(tcx, system, derived, origins, evidence, body_checks);
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

/// What each forall predicate or function is with respect to the derived predicates, by the
/// item it stands for ([`dependency::dependent_items`]). One without a recorded origin is a
/// closure's contract (dependent when some closure's specification refers to a dependent item),
/// the postcondition of a trait's method without a specification (dependent when some impl
/// method of a foreign trait has a specification that does), or else dependent.
fn forall_members<'tcx>(
    tcx: TyCtxt<'tcx>,
    derived: &HashMap<chc::UserDefinedPred, DerivedAt<'tcx>>,
    origins: &HashMap<chc::ForallPred, pred_inst::ForallPredOrigin<'tcx>>,
) -> impl Fn(&chc::ForallPred) -> ForallMember {
    let seeds: HashSet<DefId> = derived.values().map(|at| at.pred_def_id).collect();
    let dependent = dependency::dependent_items(tcx, &seeds);
    let positive_seeds: HashSet<DefId> = seeds
        .iter()
        .copied()
        .filter(|seed| !dependency::written_dependent_instance(tcx, *seed, &dependent))
        .collect();
    let specifies_dependent = |def: LocalDefId| {
        dependency::contract_fns(tcx, def)
            .iter()
            .any(|f| dependent.contains(f))
    };
    let local_defs: Vec<LocalDefId> = tcx.hir_crate_items(()).definitions().collect();
    let closures = local_defs
        .iter()
        .copied()
        .filter(|def| tcx.def_kind(*def) == DefKind::Closure)
        .any(specifies_dependent);
    let method_posts = local_defs
        .into_iter()
        .filter(|def| {
            tcx.impl_of_assoc(def.to_def_id())
                .and_then(|impl_def_id| tcx.impl_trait_ref(impl_def_id))
                .is_some_and(|trait_ref| !trait_ref.skip_binder().def_id.is_local())
        })
        .any(specifies_dependent);
    let origins: HashMap<chc::ForallPred, DefId> = origins
        .iter()
        .map(|(pred, origin)| (pred.clone(), origin.def_id))
        .collect();
    let member = |depends: bool| {
        if depends {
            ForallMember::Dependent
        } else {
            ForallMember::Independent
        }
    };
    move |pred: &chc::ForallPred| match origins.get(pred) {
        Some(def_id) if positive_seeds.contains(def_id) => ForallMember::Derived,
        Some(def_id) => member(dependent.contains(def_id)),
        None if ["q_pre_", "q_post_", "q_hist_inv_"]
            .iter()
            .any(|prefix| pred.inner().starts_with(prefix)) =>
        {
            member(closures)
        }
        None if pred.inner().starts_with("q_method_post_") => member(method_posts),
        None => ForallMember::Dependent,
    }
}

/// Condition A: each assumption the system does not discharge is walked with its polarity
/// through the bodies known here; a derived predicate must occur positively, and any other
/// member of the dependency closure reached without a body (a forall predicate at a type
/// parameter, a term) is rejected. A generic body's own precondition is walked for the
/// user-defined predicates only: the body is verified for every interpretation of its type
/// parameters' predicates, and its callers establish it at their instances.
fn check_assumptions<'tcx>(
    tcx: TyCtxt<'tcx>,
    system: &chc::System,
    derived: &HashMap<chc::UserDefinedPred, DerivedAt<'tcx>>,
    origins: &HashMap<chc::ForallPred, pred_inst::ForallPredOrigin<'tcx>>,
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
    if assumed.is_empty() {
        return;
    }
    let derived_preds: HashSet<&chc::UserDefinedPred> = derived.keys().collect();
    let members = forall_members(tcx, derived, origins);
    let dependence = system.dependence(&derived_preds, &members);
    let mut reported = HashSet::new();
    for (assumption, span, formula) in &assumed {
        let exempt = matches!(assumption, Assumption::OwnRequires);
        for violation in dependence.violations(formula, exempt) {
            if !reported.insert((*span, violation.clone())) {
                continue;
            }
            let what = match assumption {
                Assumption::OwnRequires => {
                    "this function's own precondition, which only this \
                                            crate's callers establish,"
                }
                Assumption::CallEnsures(_) => {
                    "the postcondition of this call, whose callee's \
                                               body is not analyzed,"
                }
            };
            tcx.dcx().span_err(
                *span,
                format!(
                    "{what} assumes {violation}, of a derived predicate's dependency closure; a \
                     larger relation than the least one could make it stronger than stated; \
                     define the predicate in the impl"
                ),
            );
        }
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
