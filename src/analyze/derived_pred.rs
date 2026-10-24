//! Derived predicates: a trait's `#[thrust_macros::predicate(derived)]` at an impl that leaves
//! it undefined.
//!
//! Such a predicate `P` is an unknown of the query, inferred with the rest as a loop invariant
//! or an omitted contract is: the impl's functions and laws are checked against the trait's
//! contracts with `P` in them, as with a written body, and the solver picks a relation that makes
//! every clause hold. A solution `σ` is then a typing of every analyzed body with `P := σ(P)`
//! written, so the program is safe by the soundness of the type system, whatever `σ(P)` is. The
//! verdict says nothing of `P`'s meaning beyond that. Two conditions make it so:
//!
//! - `P` is one relation that depends on no forall predicate: it is declared with the empty
//!   dependency set (`chc::smtlib2`), so a law of a trait over a forall predicate cannot have
//!   `P` chosen after it;
//! - no contract Thrust assumes without checking it against a body (a trusted, ignored or
//!   unselected function, a trusted impl method or default method, an extern specification of a
//!   foreign function, `std.rs`, an inherited law not checked for its impl) mentions `P` or a
//!   predicate whose definition may depend on it, in any polarity: such a contract is the user's
//!   statement of a relation that `σ(P)` need not be. [`check`] rejects one.
//!
//! An analyzed function whose own precondition mentions `P` and which code Thrust does not analyze
//! may enter is handled as one whose precondition is inferred, by the entry rule of
//! `unanalyzed_entry`: its precondition must hold of every argument there.
//!
//! A generic impl may leave `P` out only when each instance is analyzed
//! (`THRUST_PER_INSTANCE_GENERICS=1`): each concrete instance is then an unknown of its own, the
//! impl's functions are analyzed there, and the laws of [`per_instance_law_impls`] are checked at
//! every instance the crate uses ([`check_law_uses`]). A solution is a written body per instance,
//! which types the program instance by instance.

mod dependency;

use std::collections::{HashMap, HashSet};

use rustc_hir::def::DefKind;
use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeVisitableExt as _};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze::{self, BodyCheck, BodyChecks};
use crate::chc;

/// A derived predicate: the trait item `pred_def_id`, left out by an impl of the crate.
#[derive(Debug, Clone, Copy)]
pub struct DerivedAt {
    pub pred_def_id: DefId,
}

impl DerivedAt {
    /// The derived predicate `pred_def_id` at `generic_args`, when an impl of the crate is for
    /// exactly their trait arguments, or, with `per_instance`, when they are concrete and select
    /// an impl of the crate, generic or not ([`generic_impl_instance`]). `None` otherwise: an
    /// instance whose relation would have to be one per instance of a generic impl verified once.
    pub fn new<'tcx>(
        tcx: TyCtxt<'tcx>,
        pred_def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        per_instance: bool,
    ) -> Option<Self> {
        let trait_def_id = tcx.trait_of_assoc(pred_def_id)?;
        let trait_args = generic_args.truncate_to(tcx, tcx.generics_of(trait_def_id));
        let trait_ref = tcx.erase_regions(mir_ty::TraitRef::new(tcx, trait_def_id, trait_args));
        let concrete_impl = tcx.all_impls(trait_def_id).any(|impl_def_id| {
            let impl_ref = tcx.impl_trait_ref(impl_def_id).unwrap();
            let impl_ref = tcx.erase_regions(impl_ref.instantiate_identity());
            !impl_ref.has_param() && impl_ref == trait_ref
        });
        let instance =
            per_instance && generic_impl_instance(tcx, pred_def_id, generic_args).is_some();
        (concrete_impl || instance).then_some(Self { pred_def_id })
    }
}

/// The local generic impl that concrete `generic_args` of the trait item `pred_def_id` select,
/// with the trait's arguments there: an instance of a generic impl, at which a derived predicate
/// it leaves out is one unknown of its own.
pub fn generic_impl_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    pred_def_id: DefId,
    generic_args: mir_ty::GenericArgsRef<'tcx>,
) -> Option<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
    let trait_def_id = tcx.trait_of_assoc(pred_def_id)?;
    let trait_args =
        tcx.erase_regions(generic_args.truncate_to(tcx, tcx.generics_of(trait_def_id)));
    let (impl_def_id, _) = select_generic_impl(tcx, trait_def_id, trait_args)?;
    Some((impl_def_id, trait_args))
}

/// The local generic impl of `trait_def_id` that the concrete `trait_args` select, with the impl's
/// own arguments there.
pub fn select_generic_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
    trait_args: mir_ty::GenericArgsRef<'tcx>,
) -> Option<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
    if trait_args.has_param() {
        return None;
    }
    let trait_ref = mir_ty::TraitRef::new(tcx, trait_def_id, trait_args);
    let typing_env = mir_ty::TypingEnv::fully_monomorphized();
    let source = tcx
        .codegen_select_candidate(typing_env.as_query_input(trait_ref))
        .ok()?;
    let rustc_middle::traits::ImplSource::UserDefined(data) = source else {
        return None;
    };
    let impl_ref = tcx.impl_trait_ref(data.impl_def_id)?.instantiate_identity();
    (data.impl_def_id.is_local() && impl_ref.has_param()).then_some((data.impl_def_id, data.args))
}

/// The local generic impls whose laws are checked at each instance (`THRUST_PER_INSTANCE_GENERICS`)
/// rather than once over their type parameters: those for a type whose local impls of a trait all
/// leave a derived predicate out, of a trait with a law whose contract mentions that predicate or
/// one whose definition may depend on it. Over the type parameters the predicate is no relation;
/// at each instance it is an unknown of its own, which the law is checked of.
pub fn per_instance_law_impls(
    tcx: TyCtxt<'_>,
    trait_laws: &rustc_data_structures::fx::FxIndexMap<DefId, Vec<DefId>>,
) -> HashSet<DefId> {
    let self_adt = |impl_def_id: DefId| {
        tcx.type_of(impl_def_id)
            .instantiate_identity()
            .ty_adt_def()
            .map(|adt| adt.did())
    };
    let derived = tcx.hir_crate_items(()).definitions().filter(|def| {
        tcx.get_attrs_by_path(def.to_def_id(), &analyze::annot::derived_path())
            .next()
            .is_some()
    });
    let contracts = Contracts::new(tcx);
    let mut out = HashSet::new();
    for pred in derived {
        let pred = pred.to_def_id();
        let Some(trait_def_id) = tcx.trait_of_assoc(pred) else {
            continue;
        };
        // The types whose local impls of the trait all leave the predicate out.
        let mut leaves_out: HashMap<DefId, bool> = HashMap::new();
        for impl_def_id in tcx
            .all_local_trait_impls(())
            .get(&trait_def_id)
            .into_iter()
            .flatten()
        {
            let impl_def_id = impl_def_id.to_def_id();
            let Some(adt) = self_adt(impl_def_id) else {
                continue;
            };
            let left_out = !tcx
                .impl_item_implementor_ids(impl_def_id)
                .contains_key(&pred)
                && tcx
                    .impl_trait_ref(impl_def_id)
                    .unwrap()
                    .instantiate_identity()
                    .has_param();
            *leaves_out.entry(adt).or_insert(true) &= left_out;
        }
        let dependent = dependency::dependent_items(tcx, &HashSet::from([pred]));
        for (law_trait, laws) in trait_laws {
            let mentions = laws
                .iter()
                .any(|law| contracts.of(*law).iter().any(|f| dependent.contains(f)));
            if !mentions {
                continue;
            }
            let impls = tcx
                .all_local_trait_impls(())
                .get(law_trait)
                .into_iter()
                .flatten();
            out.extend(
                impls
                    .map(|impl_def_id| impl_def_id.to_def_id())
                    .filter(|impl_def_id| {
                        self_adt(*impl_def_id)
                            .is_some_and(|adt| leaves_out.get(&adt) == Some(&true))
                    }),
            );
        }
    }
    out
}

/// Reports each use of a trait law's contract that relies on an impl of `per_instance` without the
/// law checked there: at concrete arguments that select such an impl, or at type parameters where
/// a local impl of the law's trait is one.
pub fn check_law_uses<'tcx>(
    tcx: TyCtxt<'tcx>,
    per_instance: &HashSet<DefId>,
    law_uses: &[(DefId, mir_ty::GenericArgsRef<'tcx>)],
    checked: &HashSet<(DefId, mir_ty::GenericArgsRef<'tcx>)>,
) {
    let mut reported = HashSet::new();
    for &(law, args) in law_uses {
        let Some(trait_def_id) = tcx.trait_of_assoc(law) else {
            continue;
        };
        let trait_args = tcx.erase_regions(args.truncate_to(tcx, tcx.generics_of(trait_def_id)));
        if checked.contains(&(law, trait_args)) || !reported.insert((law, trait_args)) {
            continue;
        }
        let relies = if trait_args.has_param() {
            per_instance
                .iter()
                .any(|impl_def_id| tcx.trait_id_of_impl(*impl_def_id) == Some(trait_def_id))
        } else {
            select_generic_impl(tcx, trait_def_id, trait_args)
                .is_some_and(|(impl_def_id, _)| per_instance.contains(&impl_def_id))
        };
        if relies {
            tcx.dcx().span_err(
                tcx.def_span(law),
                format!(
                    "the law `{}` is assumed at `{}`, where it is checked only at each instance \
                     of an impl that leaves a derived predicate out, and is not checked there",
                    tcx.item_name(law),
                    trait_args.type_at(0)
                ),
            );
        }
    }
}

/// The written contracts of the crate by the function they are of: a function's own, and those
/// an extern specification (`#[thrust::extern_spec_fn]`, also a trait method's, which the trait
/// writes on one) states of its target.
struct Contracts<'tcx> {
    tcx: TyCtxt<'tcx>,
    by_target: HashMap<DefId, Vec<LocalDefId>>,
}

impl<'tcx> Contracts<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        let mut by_target: HashMap<DefId, Vec<LocalDefId>> = HashMap::new();
        for def in tcx.hir_crate_items(()).definitions() {
            // `std.rs` states the library's behaviour for every implementation of its traits'
            // predicates and every closure contract, as a generic function verified once holds
            // for every interpretation: its specifications are trusted to be parametric.
            if !is_extern_spec(tcx, def.to_def_id()) || analyze::is_injected_std(tcx, def) {
                continue;
            }
            // The specification's body is its contract's path statements and a tail call of
            // the target.
            let contract: HashSet<DefId> = dependency::contract_fns(tcx, def).into_iter().collect();
            for target in dependency::referenced_fns(tcx, def) {
                if !contract.contains(&target) {
                    by_target.entry(target).or_default().push(def);
                }
            }
        }
        Self { tcx, by_target }
    }

    /// The formula functions of every contract written for `def_id`.
    fn of(&self, def_id: DefId) -> Vec<DefId> {
        let own = def_id
            .as_local()
            .map(|local| dependency::contract_fns(self.tcx, local))
            .unwrap_or_default();
        let specs = self.by_target.get(&def_id).into_iter().flatten();
        own.into_iter()
            .chain(specs.flat_map(|spec| dependency::contract_fns(self.tcx, *spec)))
            .collect()
    }

    /// The formula functions of the contracts assumed for `def_id`: for an impl method without
    /// one of its own, the trait's for the method too.
    fn assumed_for(&self, def_id: DefId) -> Vec<DefId> {
        let mut fns = self.of(def_id);
        let trait_item = self
            .tcx
            .opt_associated_item(def_id)
            .and_then(|item| item.trait_item_def_id);
        if let (true, Some(trait_item)) = (fns.is_empty(), trait_item) {
            fns = self.of(trait_item);
        }
        fns
    }
}

fn is_extern_spec(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.get_attrs_by_path(def_id, &analyze::annot::extern_spec_fn_path())
        .next()
        .is_some()
}

fn is_formula_fn(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.get_attrs_by_path(def_id, &analyze::annot::formula_fn_path())
        .next()
        .is_some()
}

/// Reports each contract Thrust assumes without checking it against a body that mentions a
/// derived predicate of `derived`, or a predicate whose definition may depend on one, and stops
/// if there is one.
pub fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    derived: &HashMap<chc::UserDefinedPred, DerivedAt>,
    body_checks: &BodyChecks,
    trait_laws: &rustc_data_structures::fx::FxIndexMap<DefId, Vec<DefId>>,
    inherited_laws_checked: &HashSet<(DefId, DefId)>,
    per_instance: &HashSet<DefId>,
    closure_contract_fns: [Option<DefId>; 3],
) {
    let mut seeds: HashSet<DefId> = derived.values().map(|at| at.pred_def_id).collect();
    // A raw SMT-LIB2 body may name a derived predicate's symbol, and the closure cannot read it,
    // so every raw-body predicate is taken to depend on one.
    seeds.extend(
        tcx.hir_crate_items(())
            .definitions()
            .filter(|def| dependency::is_raw_predicate(tcx, *def))
            .map(LocalDefId::to_def_id),
    );
    let mut dependent = dependency::dependent_items(tcx, &seeds);
    // `pre!`, `post!` and `hist_inv!` of a closure at a type parameter stand for the contract of
    // whatever closure it is instantiated with, so they depend on a derived predicate when some
    // closure's written specification does.
    let closure_depends = tcx.hir_body_owners().any(|def| {
        tcx.def_kind(def) == DefKind::Closure
            && dependency::contract_fns(tcx, def)
                .iter()
                .any(|f| dependent.contains(f))
    });
    if closure_depends {
        seeds.extend(closure_contract_fns.iter().flatten());
        dependent = dependency::dependent_items(tcx, &seeds);
    }
    let contracts = Contracts::new(tcx);
    let mentions = |fns: &[DefId]| fns.iter().any(|f| dependent.contains(f));
    let report = |def_id: DefId, what: &str| {
        tcx.dcx().span_err(
            tcx.def_span(def_id),
            format!(
                "{what}, assumed without being checked against a body, mentions a derived \
                 predicate or one whose definition depends on it, whose inferred relation it \
                 need not hold of; define the predicate in the impl, or check the body"
            ),
        );
    };
    for def in tcx.hir_crate_items(()).definitions() {
        let def_id = def.to_def_id();
        let is_fn = matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn);
        // A trait's law is checked per impl, below.
        let trait_law = tcx.trait_of_assoc(def_id).is_some()
            && tcx
                .get_attrs_by_path(def_id, &analyze::annot::law_path())
                .next()
                .is_some();
        let skipped = is_extern_spec(tcx, def_id)
            || is_formula_fn(tcx, def_id)
            || analyze::is_injected_std(tcx, def)
            || trait_law;
        if !is_fn || skipped {
            continue;
        }
        // A trait method without a body is checked at each impl that is analyzed.
        if tcx.hir_maybe_body_owned_by(def).is_none() {
            continue;
        }
        let check = body_checks.get(def);
        if matches!(check, Some(BodyCheck::Checked | BodyCheck::Specification)) {
            continue;
        }
        if mentions(&contracts.assumed_for(def_id)) {
            let status = check.map_or("not analyzed", BodyCheck::status);
            report(
                def_id,
                &format!("the contract of `{}` ({status})", tcx.item_name(def_id)),
            );
        }
    }
    // The extern specifications of functions of other crates.
    for (target, specs) in &contracts.by_target {
        if target.is_local() || !mentions(&contracts.of(*target)) {
            continue;
        }
        for spec in specs {
            report(
                spec.to_def_id(),
                &format!("the specification of `{}`", tcx.def_path_str(*target)),
            );
        }
    }
    // Inherited laws, checked per impl; those of an impl of `per_instance` at each instance where
    // one is used ([`check_law_uses`]).
    for (trait_def_id, laws) in trait_laws {
        let impls = tcx
            .all_local_trait_impls(())
            .get(trait_def_id)
            .into_iter()
            .flatten();
        for impl_def_id in impls {
            let impl_def_id = impl_def_id.to_def_id();
            if per_instance.contains(&impl_def_id) {
                continue;
            }
            let implemented = tcx.impl_item_implementor_ids(impl_def_id);
            for &law in laws {
                let inherited = !implemented.contains_key(&law);
                let checked = inherited_laws_checked.contains(&(impl_def_id, law));
                if inherited && !checked && mentions(&contracts.of(law)) {
                    report(
                        law,
                        &format!(
                            "the law `{}`, not checked for `{}`",
                            tcx.item_name(law),
                            tcx.type_of(impl_def_id).instantiate_identity()
                        ),
                    );
                }
            }
        }
    }
    tcx.dcx().abort_if_errors();
}
