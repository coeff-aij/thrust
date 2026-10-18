//! Extern specs at calls: which calls a spec covers and at which arguments, and the checks, at
//! each instance of a generic def, of what its analysis assumed at its type parameters (spec
//! bounds, bound impls and total methods).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use rustc_index::IndexVec;
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze::model_eq::{is_model_eq_clause, model_eq_bound, SpecBound};
use crate::analyze::{derive, Analyzer, DefTy, DeferredDefTy};
use crate::chc;
use crate::rty;

/// What generic analyses assumed at their type parameters, checked at each instance once every
/// body is analysed.
#[derive(Clone, Default)]
pub(super) struct SpecAssumptions<'tcx> {
    /// The spec bounds a body assumed at a type parameter or an unresolved projection, keyed by
    /// the typeck root of the def it was analysed under; see [`classify_spec_bounds`].
    assumed_spec_bounds: RefCell<HashMap<DefId, Vec<mir_ty::Clause<'tcx>>>>,
    /// The trait methods without a specification a body called, or a contract named by `pre!`, at
    /// its type parameters, keyed like `assumed_spec_bounds`; see
    /// [`Analyzer::check_reused_total_methods`].
    assumed_total_methods: RefCell<HashMap<DefId, Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)>>>,
    /// The trait methods a body called at its type parameters with the trait's specification,
    /// keyed like `assumed_spec_bounds`; see [`Analyzer::expand_dispatched_instances`].
    dispatched_calls: RefCell<HashMap<DefId, Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)>>>,
    /// The trait bounds of std impls a body called at its type parameters, keyed like
    /// `assumed_spec_bounds`; see [`Analyzer::check_reused_bound_impls`].
    assumed_bound_impls: RefCell<HashMap<DefId, Vec<mir_ty::TraitRef<'tcx>>>>,
}

/// Binds the parameters of an extern spec function to the arguments of an actual call, by
/// matching `target_args` (the spec's own tail call, in the target's parameter space) against
/// `generic_args` (the actual call's instantiation of the same target).
///
/// A parameter of the spec occurring in `target_args` is one the spec generalizes over and takes
/// whatever the actual call has at that place. Anything else the spec fixed is covered only by
/// the same type: the spec's body was checked once, against that one instantiation, and only
/// handles it. Returns `None` when the call is not covered.
pub(super) fn bind_spec_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    spec_def_id: LocalDefId,
    target_args: mir_ty::GenericArgsRef<'tcx>,
    generic_args: mir_ty::GenericArgsRef<'tcx>,
) -> Option<mir_ty::GenericArgsRef<'tcx>> {
    let mut bound = HashMap::new();
    for (spec_arg, actual_arg) in target_args.iter().zip(generic_args.iter()) {
        if !match_spec_arg(tcx, spec_arg, actual_arg, &mut bound) {
            return None;
        }
    }
    Some(mir_ty::GenericArgs::for_item(
        tcx,
        spec_def_id.to_def_id(),
        |param, _| match param.kind {
            mir_ty::GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
            _ => bound
                .get(&param.index)
                .copied()
                .unwrap_or_else(|| tcx.mk_param_from_def(param)),
        },
    ))
}

/// The bounds an extern spec puts on its type parameters by traits of its own, and the associated
/// types those fix. `Model` is left out: it is assumed of every type parameter.
fn is_spec_bound(clause: mir_ty::Clause<'_>, model_trait: DefId) -> bool {
    if clause.as_projection_clause().is_some() {
        return true;
    }
    clause.as_trait_clause().is_some_and(|clause| {
        let trait_def_id = clause.skip_binder().trait_ref.def_id;
        trait_def_id.is_local() && trait_def_id != model_trait
    })
}

/// Whether spec bounds (see [`is_spec_bound`]) hold in the environment of `caller_def_id`.
/// Returns those assumed, or the first that fails.
///
/// A spec stated through a trait (`I: IteratorSpec`) says nothing about a type that does not
/// implement it, so a call at such a type finds no specification. A bound whose self type is a
/// type parameter or an unresolved projection is assumed: the caller's contract is then verified
/// under it, and [`Analyzer::check_reused_spec_bounds`] checks it at each instance that reuses that
/// contract.
///
/// `Model` and its `PartialEq` are assumed of every type parameter of the caller, as a spec
/// assumes them of its own: they are what a bound like `usize: SliceIndexSpec<T>` needs of `T`.
fn classify_spec_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    clauses: impl IntoIterator<Item = mir_ty::Clause<'tcx>>,
    caller_def_id: DefId,
    model_ty: DefId,
) -> Result<Vec<mir_ty::Clause<'tcx>>, mir_ty::Clause<'tcx>> {
    use rustc_infer::infer::TyCtxtInferExt as _;

    let typing_env = model_assuming_env(tcx, caller_def_id, model_ty);
    let infcx = tcx.infer_ctxt().build(typing_env.typing_mode);
    let mut assumed = Vec::new();
    for clause in clauses {
        let bound = match clause.as_projection_clause() {
            Some(projection) => projection_bound(tcx, typing_env, projection.skip_binder()),
            None if is_model_eq_clause(tcx, clause) => model_eq_bound(tcx, typing_env, clause),
            None => trait_bound(tcx, &infcx, typing_env, clause),
        };
        match bound {
            SpecBound::Holds => {}
            SpecBound::Assumed => assumed.push(clause),
            SpecBound::Fails => return Err(clause),
        }
    }
    Ok(assumed)
}

fn trait_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    infcx: &rustc_infer::infer::InferCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    clause: mir_ty::Clause<'tcx>,
) -> SpecBound {
    use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;
    use rustc_trait_selection::traits::{Obligation, ObligationCause};

    // A higher-ranked bound (`for<'a> &'a T: Tr`) is read with its bound regions erased, which
    // trait selection modulo regions decides as it decides the bound.
    let pred = clause.as_trait_clause().unwrap();
    let trait_ref = tcx.instantiate_bound_regions_with_erased(pred).trait_ref;
    let Ok(trait_ref) = tcx.try_normalize_erasing_regions(typing_env, trait_ref) else {
        return SpecBound::Assumed;
    };
    let obligation = Obligation::new(
        tcx,
        ObligationCause::dummy(),
        typing_env.param_env,
        trait_ref,
    );
    if infcx.predicate_must_hold_modulo_regions(&obligation) {
        return SpecBound::Holds;
    }
    if matches!(
        trait_ref.self_ty().kind(),
        mir_ty::TyKind::Param(_) | mir_ty::TyKind::Alias(..)
    ) {
        SpecBound::Assumed
    } else {
        SpecBound::Fails
    }
}

/// Whether an associated type a spec's bound fixes (`R: IntoSliceIdx<I, [T], Output = usize>`)
/// is that type at the arguments the spec was bound to. A spec's contract is stated for the type it
/// fixes: at another one the target's result is not the one the contract describes. A projection
/// that stays unresolved is assumed, like a bound on a type parameter.
fn projection_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    projection: mir_ty::ProjectionPredicate<'tcx>,
) -> SpecBound {
    let normalize = |term| tcx.try_normalize_erasing_regions(typing_env, term).ok();
    let (Some(actual), Some(fixed)) = (
        normalize(projection.projection_term.to_term(tcx)),
        normalize(projection.term),
    ) else {
        return SpecBound::Assumed;
    };
    if actual == fixed {
        return SpecBound::Holds;
    }
    let unresolved = actual.as_type().is_some_and(|ty| {
        matches!(
            ty.kind(),
            mir_ty::TyKind::Param(_) | mir_ty::TyKind::Alias(..)
        )
    });
    if unresolved {
        SpecBound::Assumed
    } else {
        SpecBound::Fails
    }
}

/// The environment a predicate call in `owner_fn_id` is resolved in: the owner's own, with `Model`
/// assumed of its type parameters as a spec assumes it, so that a call on a concrete type is
/// resolved to the impl's predicate even when the impl needs `T: Model` of a type parameter `T`.
pub(super) fn predicate_typing_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner_fn_id: DefId,
    model_ty: Option<DefId>,
) -> mir_ty::TypingEnv<'tcx> {
    match model_ty {
        Some(model_ty) => model_assuming_env(tcx, owner_fn_id, model_ty),
        None => mir_ty::TypingEnv::post_analysis(tcx, owner_fn_id),
    }
}

fn model_assuming_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    model_ty: DefId,
) -> mir_ty::TypingEnv<'tcx> {
    use mir_ty::Upcast as _;
    let env = mir_ty::TypingEnv::post_analysis(tcx, caller_def_id);
    let model_trait = tcx.parent(model_ty);
    let Some(eq_trait) = tcx.lang_items().eq_trait() else {
        return env;
    };
    let generics = tcx.generics_of(caller_def_id);
    let assumed = (0..generics.count())
        .map(|idx| generics.param_at(idx, tcx))
        .filter(|param| matches!(param.kind, mir_ty::GenericParamDefKind::Type { .. }))
        .map(|param| tcx.mk_param_from_def(param).expect_ty())
        .flat_map(|ty| {
            let model = mir_ty::Ty::new_projection(tcx, model_ty, [ty]);
            [
                mir_ty::TraitRef::new(tcx, model_trait, [ty]).upcast(tcx),
                mir_ty::TraitRef::new(tcx, eq_trait, [model, model]).upcast(tcx),
            ]
        });
    let clauses = tcx.mk_clauses_from_iter(env.param_env.caller_bounds().iter().chain(assumed));
    mir_ty::TypingEnv {
        param_env: mir_ty::ParamEnv::new(clauses),
        ..env
    }
}

fn match_spec_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    spec_arg: mir_ty::GenericArg<'tcx>,
    actual_arg: mir_ty::GenericArg<'tcx>,
    bound: &mut HashMap<u32, mir_ty::GenericArg<'tcx>>,
) -> bool {
    use mir_ty::GenericArgKind as K;
    match (spec_arg.kind(), actual_arg.kind()) {
        (K::Lifetime(_), K::Lifetime(_)) => true,
        (K::Type(spec_ty), K::Type(actual_ty)) => match_spec_ty(tcx, spec_ty, actual_ty, bound),
        (K::Const(spec_ct), K::Const(actual_ct)) => match spec_ct.kind() {
            mir_ty::ConstKind::Param(p) => bind_spec_param(tcx, p.index, actual_arg, bound),
            _ => spec_ct == actual_ct,
        },
        _ => false,
    }
}

fn match_spec_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    spec_ty: mir_ty::Ty<'tcx>,
    actual_ty: mir_ty::Ty<'tcx>,
    bound: &mut HashMap<u32, mir_ty::GenericArg<'tcx>>,
) -> bool {
    use mir_ty::TyKind as T;
    use mir_ty::TypeVisitableExt as _;
    match (spec_ty.kind(), actual_ty.kind()) {
        (T::Param(p), _) => bind_spec_param(tcx, p.index, actual_ty.into(), bound),
        (T::Adt(spec_def, spec_args), T::Adt(actual_def, actual_args)) => {
            spec_def == actual_def
                && spec_args
                    .iter()
                    .zip(actual_args.iter())
                    .all(|(s, a)| match_spec_arg(tcx, s, a, bound))
        }
        (T::Array(spec_elem, spec_len), T::Array(actual_elem, actual_len)) => {
            match_spec_ty(tcx, *spec_elem, *actual_elem, bound)
                && match_spec_arg(tcx, (*spec_len).into(), (*actual_len).into(), bound)
        }
        (T::Slice(spec_elem), T::Slice(actual_elem)) => {
            match_spec_ty(tcx, *spec_elem, *actual_elem, bound)
        }
        (T::Ref(_, spec_inner, spec_mut), T::Ref(_, actual_inner, actual_mut)) => {
            spec_mut == actual_mut && match_spec_ty(tcx, *spec_inner, *actual_inner, bound)
        }
        (T::Tuple(spec_tys), T::Tuple(actual_tys)) => {
            spec_tys.len() == actual_tys.len()
                && spec_tys
                    .iter()
                    .zip(actual_tys.iter())
                    .all(|(s, a)| match_spec_ty(tcx, s, a, bound))
        }
        _ => !spec_ty.has_param() && tcx.erase_regions(spec_ty) == tcx.erase_regions(actual_ty),
    }
}

fn bind_spec_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    index: u32,
    actual_arg: mir_ty::GenericArg<'tcx>,
    bound: &mut HashMap<u32, mir_ty::GenericArg<'tcx>>,
) -> bool {
    let actual_arg = tcx.erase_regions(actual_arg);
    *bound.entry(index).or_insert(actual_arg) == actual_arg
}

/// The supertrait bounds `bound` implies (`T: PartialOrd` of `T: Ord`), which a callee bounded by
/// `bound` may rely on too.
pub(super) fn supertrait_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    bound: mir_ty::TraitRef<'tcx>,
) -> Vec<mir_ty::TraitRef<'tcx>> {
    tcx.explicit_super_predicates_of(bound.def_id)
        .iter_instantiated_copied(tcx, bound.args)
        .filter_map(|(clause, _)| clause.as_trait_clause())
        .map(|pred| tcx.instantiate_bound_regions_with_erased(pred).trait_ref)
        .collect()
}

/// How deeply the types in `arg` nest.
pub(super) fn type_depth(arg: mir_ty::GenericArg<'_>) -> usize {
    let mut walker = arg.walk();
    walker.next();
    let mut depth = 0;
    while let Some(child) = walker.next() {
        depth = depth.max(type_depth(child));
        walker.skip_current_subtree();
    }
    depth + 1
}

/// The generic arguments of a trait or projection clause, which [`type_depth`] measures.
fn clause_args<'tcx>(clause: &mir_ty::Clause<'tcx>) -> Vec<mir_ty::GenericArg<'tcx>> {
    if let Some(pred) = clause.as_trait_clause() {
        return pred.skip_binder().trait_ref.args.to_vec();
    }
    if let Some(pred) = clause.as_projection_clause() {
        return pred.skip_binder().projection_term.args.to_vec();
    }
    Vec::new()
}

/// A trait method at generic arguments.
type MethodCall<'tcx> = (DefId, mir_ty::GenericArgsRef<'tcx>);

/// A def whose generic contract is reused at generic arguments, and the caller that reuses it.
type ReusedInstance<'tcx> = (DefId, mir_ty::GenericArgsRef<'tcx>, DefId);

fn instantiate_method_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    (method, method_args): MethodCall<'tcx>,
    args: mir_ty::GenericArgsRef<'tcx>,
) -> MethodCall<'tcx> {
    (
        method,
        mir_ty::EarlyBinder::bind(method_args).instantiate(tcx, args),
    )
}

/// The trait bounds `def_id` puts on `args`, its own and its parent's.
pub fn trait_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: mir_ty::GenericArgsRef<'tcx>,
) -> Vec<mir_ty::TraitRef<'tcx>> {
    tcx.predicates_of(def_id)
        .instantiate(tcx, args)
        .predicates
        .into_iter()
        .filter_map(|clause| clause.as_trait_clause())
        .filter(|pred| pred.skip_binder().polarity == mir_ty::PredicatePolarity::Positive)
        .map(|pred| tcx.instantiate_bound_regions_with_erased(pred).trait_ref)
        .map(|trait_ref| tcx.erase_regions(trait_ref))
        .collect()
}

impl<'tcx> Analyzer<'tcx> {
    /// The generic arguments of `spec` at a call of its target at `generic_args`, or `None` when
    /// the spec does not cover the call.
    ///
    /// A def_id key can be a blanket impl shared by more instantiations than an extern spec's own
    /// tail call covers (e.g. `Vec::index` at some `Idx` other than the `usize`
    /// `_extern_spec_vec_index` calls it at). Handing such a call that spec's contract would relate
    /// its result to whatever the spec's own body happens to return, regardless of the real `Idx`
    /// here.
    pub(super) fn spec_args(
        &self,
        spec: &DeferredDefTy<'tcx>,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> Option<mir_ty::GenericArgsRef<'tcx>> {
        let Some(target_args) = spec.target_args else {
            return Some(generic_args);
        };
        let bound = bind_spec_args(self.tcx, spec.local_def_id, target_args, generic_args)?;
        let Some(model_ty) = self.def_ids().model_ty() else {
            return Some(bound);
        };
        let model_trait = self.tcx.parent(model_ty);
        let type_builder = self.type_builder(self.def_ids(), caller_def_id);
        let clauses = self
            .tcx
            .predicates_of(spec.local_def_id)
            .instantiate(self.tcx, bound)
            .predicates
            .into_iter()
            .filter(|clause| is_spec_bound(*clause, model_trait))
            .filter(|clause| {
                !derive::holds_by_generated_compares(
                    self.tcx,
                    &self.def_ids(),
                    &type_builder,
                    *clause,
                )
            });
        let assumed = classify_spec_bounds(self.tcx, clauses, caller_def_id, model_ty).ok()?;
        self.record_assumed_spec_bounds(caller_def_id, assumed);
        Some(bound)
    }

    /// Records spec bounds assumed while analysing a body owned by `owner_fn_id`, under its typeck
    /// root: a closure's body is verified as part of the fn it is in. Returns whether any is new.
    fn record_assumed_spec_bounds(
        &self,
        owner_fn_id: DefId,
        clauses: Vec<mir_ty::Clause<'tcx>>,
    ) -> bool {
        let root = self.tcx.typeck_root_def_id(owner_fn_id);
        let mut assumed = self.spec_assumptions.assumed_spec_bounds.borrow_mut();
        let recorded = assumed.entry(root).or_default();
        let mut grew = false;
        for clause in clauses {
            let clause = self.tcx.erase_regions(clause);
            if !recorded.contains(&clause) {
                recorded.push(clause);
                grew = true;
            }
        }
        grew
    }

    /// Checks the spec bounds each generic def's analysis assumed at its type parameters
    /// ([`classify_spec_bounds`]) at every instance that uses its contract as instantiated.
    ///
    /// Creusot requires such a bound (`T::IntoIter: IteratorSpec` of `FromIterator::from_iter`'s
    /// extern spec) to be provable at each call, so a generic caller must declare it and rustc
    /// checks it at the caller's instantiations. Here the bound is assumed at the caller's type
    /// parameters instead, so this checks it at each instance, after every body is analysed, when
    /// all the assumptions are known. A bound still at a type parameter of the instance's caller
    /// is assumed by that caller in turn, until nothing new is assumed. A program with an instance
    /// at which a bound fails is rejected: the generic contract does not stand for it, and its
    /// body would call a spec that does not cover it, as a direct call there does.
    fn check_reused_spec_bounds(&mut self, seen: &mut HashSet<(mir_ty::Clause<'tcx>, DefId)>) {
        let Some(model_ty) = self.def_ids().model_ty() else {
            return;
        };
        self.propagate_reused(
            |this| &this.spec_assumptions.assumed_spec_bounds,
            |tcx, clause, args| mir_ty::EarlyBinder::bind(clause).instantiate(tcx, args),
            clause_args,
            seen,
            |this, clause, (def_id, generic_args, caller_def_id)| match classify_spec_bounds(
                this.tcx,
                [clause],
                caller_def_id,
                model_ty,
            ) {
                Ok(assumed) => this.record_assumed_spec_bounds(caller_def_id, assumed),
                Err(clause) => this.tcx.dcx().fatal(format!(
                    "spec bound not satisfied: `{}` is verified generically under a spec \
                         bound at its type parameters, which does not hold at its instance \
                         `{}` used in `{}`: `{clause}`",
                    this.tcx.def_path_str(def_id),
                    this.tcx.def_path_str_with_args(def_id, generic_args),
                    this.tcx.def_path_str(caller_def_id),
                )),
            },
        );
    }

    /// Records that a body analysed under `owner_fn_id` called the trait method `def_id` at
    /// `generic_args` that name type parameters, taking the trait's specification. Returns
    /// whether it is new.
    pub fn record_dispatched_call(
        &self,
        owner_fn_id: DefId,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> bool {
        let root = self.tcx.typeck_root_def_id(owner_fn_id);
        let call = (def_id, self.tcx.erase_regions(generic_args));
        let mut dispatched = self.spec_assumptions.dispatched_calls.borrow_mut();
        let recorded = dispatched.entry(root).or_default();
        if recorded.contains(&call) {
            return false;
        }
        recorded.push(call);
        true
    }

    /// Adds to the reused instances the impl methods that a reused generic body reaches through
    /// a trait method called at its type parameters ([`Self::record_dispatched_call`]), resolved at
    /// the instance's arguments, to a fixpoint. A generic impl method verified once may assume
    /// spec bounds or total methods at its own type parameters, and an instance reached only
    /// through such a call would otherwise never check them. A call still at a type parameter of
    /// the instance's caller is recorded for that caller in turn.
    fn expand_dispatched_instances(&mut self, seen: &mut HashSet<(MethodCall<'tcx>, DefId)>) {
        use mir_ty::TypeVisitableExt as _;

        self.propagate_reused(
            |this| &this.spec_assumptions.dispatched_calls,
            instantiate_method_call,
            |(_, args)| args.to_vec(),
            seen,
            |this, (method, method_args), (_, _, caller_def_id)| {
                if method_args.has_param() {
                    return this.record_dispatched_call(caller_def_id, method, method_args);
                }
                let typing_env = mir_ty::TypingEnv::fully_monomorphized();
                let Ok(Some(instance)) =
                    mir_ty::Instance::try_resolve(this.tcx, typing_env, method, method_args)
                else {
                    return false;
                };
                if !instance.def_id().is_local()
                    || !matches!(this.defs.get(&instance.def_id()), Some(DefTy::Generic(_)))
                {
                    return false;
                }
                let reached = (instance.def_id(), instance.args, caller_def_id);
                let mut reused = this.reused_generic_instances.borrow_mut();
                if reused.contains(&reached) {
                    return false;
                }
                reused.push(reached);
                true
            },
        );
    }

    /// Follows `bounds`, which a call of a std function or a trusted derive in `owner_fn_id`
    /// relies on, to the crate impls they select, whose methods at the selected arguments become
    /// reused instances ([`Self::reuse_impl_methods`]), and records for `owner_fn_id` the bounds
    /// at its type parameters. A std function's specification, the trait's or its own, holds
    /// only where the impls its trait bounds select meet their traits' specifications
    /// (`Option<W<F>>::clone` runs `W::clone`), which a generic impl method's analysis assumed of
    /// its own parameters. Each bound is followed through the nested obligations of the impl that
    /// trait selection picks for it, a std impl's, a crate impl's or a builtin one (the `Clone` of
    /// a tuple); a bound at a type parameter is followed at each instance that reuses the
    /// contract of the body ([`Self::check_reused_bound_impls`]).
    pub fn check_bound_impls(
        &self,
        owner_fn_id: DefId,
        typing_env: mir_ty::TypingEnv<'tcx>,
        bounds: Vec<mir_ty::TraitRef<'tcx>>,
    ) -> bool {
        let mut grew = false;
        let on_crate_impl = &mut |impl_def_id, args| {
            grew |= self.reuse_impl_methods(impl_def_id, args, owner_fn_id);
        };
        let at_params = self.select_bound_impls(owner_fn_id, typing_env, bounds, on_crate_impl);
        for bound in at_params {
            grew |= self.record_assumed_bound_impl(owner_fn_id, bound);
        }
        grew
    }

    /// Follows `bounds` through the impls trait selection picks for them in `typing_env`: each
    /// bound normalized, with its supertraits, through the nested obligations of a std impl, a
    /// crate impl (passed to `on_crate_impl` at its selected arguments) or a builtin one. Returns
    /// the bounds left at a type parameter. A bound that selects no impl stops the analysis.
    fn select_bound_impls(
        &self,
        owner_fn_id: DefId,
        typing_env: mir_ty::TypingEnv<'tcx>,
        bounds: Vec<mir_ty::TraitRef<'tcx>>,
        on_crate_impl: &mut dyn FnMut(DefId, mir_ty::GenericArgsRef<'tcx>),
    ) -> Vec<mir_ty::TraitRef<'tcx>> {
        use mir_ty::TypeVisitableExt as _;
        use rustc_infer::infer::TyCtxtInferExt as _;
        use rustc_middle::traits::ImplSource;
        use rustc_trait_selection::traits::{Obligation, ObligationCause, SelectionContext};

        let (infcx, param_env) = self.tcx.infer_ctxt().build_with_typing_env(typing_env);
        let mut selcx = SelectionContext::new(&infcx);
        let mut at_params = Vec::new();
        let mut visited = HashSet::new();
        let mut pending = bounds;
        while let Some(bound) = pending.pop() {
            let bound = self
                .tcx
                .try_normalize_erasing_regions(typing_env, bound)
                .unwrap_or(bound);
            if !visited.insert(bound) {
                continue;
            }
            pending.extend(supertrait_bounds(self.tcx, bound));
            let obligation = Obligation::new(self.tcx, ObligationCause::dummy(), param_env, bound);
            let nested = match selcx.select(&obligation) {
                Ok(Some(ImplSource::UserDefined(data))) => {
                    if data.impl_def_id.is_local() {
                        let args = self
                            .tcx
                            .erase_regions(infcx.resolve_vars_if_possible(data.args));
                        on_crate_impl(data.impl_def_id, args);
                    }
                    data.nested
                }
                Ok(Some(ImplSource::Builtin(_, nested))) => nested,
                Ok(Some(ImplSource::Param(_))) => {
                    at_params.push(bound);
                    continue;
                }
                Err(_) | Ok(None) => self.tcx.dcx().fatal(format!(
                    "no impl of `{bound}` is selected for `{}`, whose callee relies on it",
                    self.tcx.def_path_str(owner_fn_id),
                )),
            };
            pending.extend(nested.into_iter().filter_map(|obligation| {
                let predicate = infcx.resolve_vars_if_possible(obligation.predicate);
                let pred = predicate.as_trait_clause()?;
                let trait_ref = self
                    .tcx
                    .instantiate_bound_regions_with_erased(pred)
                    .trait_ref;
                let trait_ref = self.tcx.erase_regions(trait_ref);
                (!trait_ref.has_infer()).then_some(trait_ref)
            }));
        }
        at_params
    }

    /// Adds the methods of the crate's generic impl `impl_def_id`, at `impl_args`, to the instances
    /// that reuse a generic def's contract for `caller_def_id`. A std function whose specification
    /// rests on the impl runs its methods there, so the assumptions their generic analysis made at
    /// the impl's parameters (total methods, dispatched calls, spec bounds) are checked at these
    /// arguments, as at a direct call. Returns whether an instance is new.
    fn reuse_impl_methods(
        &self,
        impl_def_id: DefId,
        impl_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> bool {
        use mir_ty::TypeVisitableExt as _;

        if impl_args.is_empty() || impl_args.has_infer() {
            return false;
        }
        let mut grew = false;
        for &method in self.tcx.associated_item_def_ids(impl_def_id) {
            let own_generics = self.tcx.generics_of(method).own_requires_monomorphization();
            if !self.tcx.def_kind(method).is_fn_like() || own_generics {
                continue;
            }
            let reached = (method, impl_args, caller_def_id);
            let mut reused = self.reused_generic_instances.borrow_mut();
            if !reused.contains(&reached) {
                reused.push(reached);
                grew = true;
            }
        }
        grew
    }

    fn record_assumed_bound_impl(&self, owner_fn_id: DefId, bound: mir_ty::TraitRef<'tcx>) -> bool {
        let root = self.tcx.typeck_root_def_id(owner_fn_id);
        let bound = self.tcx.erase_regions(bound);
        let mut assumed = self.spec_assumptions.assumed_bound_impls.borrow_mut();
        let recorded = assumed.entry(root).or_default();
        if recorded.contains(&bound) {
            return false;
        }
        recorded.push(bound);
        true
    }

    /// Checks, at each instance that uses a generic def's contract as instantiated, the bounds
    /// of std impls its analysis relied on at type parameters
    /// ([`Self::check_std_call_bounds`]). A bound still at a type parameter of the instance's
    /// caller is recorded for that caller in turn.
    fn check_reused_bound_impls(&mut self, seen: &mut HashSet<(mir_ty::TraitRef<'tcx>, DefId)>) {
        self.propagate_reused(
            |this| &this.spec_assumptions.assumed_bound_impls,
            |tcx, bound, args| mir_ty::EarlyBinder::bind(bound).instantiate(tcx, args),
            |bound| bound.args.to_vec(),
            seen,
            |this, bound, (_, _, caller_def_id)| {
                let typing_env = mir_ty::TypingEnv::post_analysis(this.tcx, caller_def_id);
                this.check_bound_impls(caller_def_id, typing_env, vec![bound])
            },
        );
    }

    /// Records that a body or contract analysed under `owner_fn_id` called the trait method
    /// `def_id`, which has no specification, or named its `pre!`, at `generic_args` that name type
    /// parameters, and so took it to accept any arguments. Returns whether it is new.
    pub fn record_assumed_total_method(
        &self,
        owner_fn_id: DefId,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> bool {
        let root = self.tcx.typeck_root_def_id(owner_fn_id);
        let call = (def_id, self.tcx.erase_regions(generic_args));
        let mut assumed = self.spec_assumptions.assumed_total_methods.borrow_mut();
        let recorded = assumed.entry(root).or_default();
        if recorded.contains(&call) {
            return false;
        }
        recorded.push(call);
        true
    }

    /// Checks, at each instance that uses a generic def's contract as instantiated, that every
    /// trait method its analysis called without a specification at a type parameter
    /// ([`Self::record_assumed_total_method`]) accepts any arguments there: the precondition of
    /// the impl the call resolves to holds of all of them. A call still at a type parameter of
    /// the instance's caller is assumed by that caller in turn, as
    /// [`Self::check_reused_spec_bounds`] does with spec bounds. An impl Thrust knows no contract
    /// of is not accepted, as a direct call to it is not.
    fn check_reused_total_methods(
        &mut self,
        seen: &mut HashSet<(MethodCall<'tcx>, DefId)>,
        checked: &mut HashSet<MethodCall<'tcx>>,
    ) {
        use mir_ty::TypeVisitableExt as _;

        self.propagate_reused(
            |this| &this.spec_assumptions.assumed_total_methods,
            instantiate_method_call,
            |(_, args)| args.to_vec(),
            seen,
            |this, (method, method_args), (_, _, caller_def_id)| {
                if method_args.has_param() {
                    return this.record_assumed_total_method(caller_def_id, method, method_args);
                }
                if checked.insert((method, method_args)) {
                    this.check_total_method(method, method_args, caller_def_id);
                }
                false
            },
        );
    }

    /// Runs the checks at the instances that reuse a generic def's contract until none of them
    /// adds an instance or an assumption: an instance a check adds (resolving a dispatched call,
    /// or typing a total method) is checked in turn by all of them.
    pub fn check_reused_instances(&mut self) {
        let mut dispatched = HashSet::new();
        let mut bound_impls = HashSet::new();
        let mut total_methods = HashSet::new();
        let mut checked_methods = HashSet::new();
        let mut spec_bounds = HashSet::new();
        loop {
            let instances = self.reused_generic_instances.borrow().len();
            self.expand_dispatched_instances(&mut dispatched);
            self.check_reused_bound_impls(&mut bound_impls);
            self.check_reused_total_methods(&mut total_methods, &mut checked_methods);
            self.check_reused_spec_bounds(&mut spec_bounds);
            if self.reused_generic_instances.borrow().len() == instances {
                return;
            }
        }
    }

    /// Runs `check` on each assumption that `recorded` keeps for the typeck root of a reused
    /// instance's def, read at the instance's arguments by `instantiate`, with the instance, once
    /// per assumption and caller (`seen`), until no check reports that it recorded something and
    /// no instance is added. The assumptions a caller records for itself are checked at its own
    /// instances in turn. A def that reuses its own contract at a larger type (polymorphic
    /// recursion, `f::<T>` calling `f::<W<T>>`) would record its assumptions at ever larger
    /// types, so an assumption whose generic arguments (`type_args`) nest deeper than the crate's
    /// recursion limit stops the analysis, as rustc stops instantiating such a function.
    #[allow(clippy::too_many_arguments)]
    fn propagate_reused<T: Clone + Eq + std::hash::Hash>(
        &mut self,
        recorded: impl Fn(&Self) -> &RefCell<HashMap<DefId, Vec<T>>>,
        instantiate: impl Fn(TyCtxt<'tcx>, T, mir_ty::GenericArgsRef<'tcx>) -> T,
        type_args: impl Fn(&T) -> Vec<mir_ty::GenericArg<'tcx>>,
        seen: &mut HashSet<(T, DefId)>,
        mut check: impl FnMut(&mut Self, T, ReusedInstance<'tcx>) -> bool,
    ) {
        let mut seen_instances = 0;
        loop {
            let instances = self.reused_generic_instances.borrow().clone();
            let mut grew = instances.len() != seen_instances;
            seen_instances = instances.len();
            for instance in instances {
                let (def_id, generic_args, caller_def_id) = instance;
                let root = self.tcx.typeck_root_def_id(def_id);
                let assumed = recorded(self)
                    .borrow()
                    .get(&root)
                    .cloned()
                    .unwrap_or_default();
                for assumption in assumed {
                    let assumption = instantiate(self.tcx, assumption, generic_args);
                    let limit = self.tcx.recursion_limit().0;
                    if type_args(&assumption).into_iter().map(type_depth).max() > Some(limit) {
                        self.tcx.dcx().fatal(format!(
                            "`{}` reuses its contract at types nested deeper than the recursion \
                             limit ({limit}), as a polymorphically recursive function does, which \
                             is not supported",
                            self.tcx.def_path_str(def_id),
                        ));
                    }
                    if seen.insert((assumption.clone(), caller_def_id)) {
                        grew |= check(self, assumption, instance);
                    }
                }
            }
            if !grew {
                return;
            }
        }
    }

    fn check_total_method(
        &mut self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let Ok(Some(instance)) =
            mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, generic_args)
        else {
            return;
        };
        let Some(def_ty) = self.def_ty_with_args(instance.def_id(), instance.args, caller_def_id)
        else {
            panic!("unknown def (reached at a type parameter): {instance}");
        };
        let fn_ty = def_ty
            .ty
            .as_function()
            .expect("a method has a function type");
        let mut builder = chc::ClauseBuilder::default();
        let args: IndexVec<rty::FunctionParamIdx, _> = fn_ty
            .params
            .iter()
            .map(|param| chc::Term::var(builder.add_var(param.ty.to_sort())))
            .collect();
        let mut pre = chc::Body::top();
        for (idx, param) in fn_ty.params.iter_enumerated() {
            assert!(param.refinement.existentials.is_empty());
            pre.push_conj(param.refinement.body.clone().subst_var(|v| match v {
                rty::RefinedTypeVar::Value => args[idx].clone(),
                rty::RefinedTypeVar::Free(j) => args[j].clone(),
                rty::RefinedTypeVar::Existential(_) => unreachable!(),
            }));
        }
        let origin = chc::debug::origin::Entry::described(format!(
            "precondition of {instance} at any arguments, assumed by a generic analysis"
        ));
        let clauses = builder.head(pre, origin);
        self.extend_clauses(clauses);
    }
}
