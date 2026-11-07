//! The obligation of a closure an analyzed call hands over to code Thrust does not analyze
//! ([`crate::analyze::unanalyzed_entry`]).
//!
//! The callee's contract states, per `Fn`-bounded type parameter, the `pre!` it asks of the
//! closure, and the caller discharges it. A parameter whose `pre!` it does not state gets the
//! closure's precondition required of every argument, as Flux checks a closure against an
//! unrefined bound, at the state handed over: the captures are the terms the caller holds. An
//! `FnMut` closure the callee may call repeatedly changes its state, so its precondition is
//! required at every state its calls reach from that one: a fresh unknown `R` holds of the
//! handed-over state (E1), is closed under the closure's postcondition (E2), and implies its
//! precondition (E3).

use rustc_index::IndexVec;
use rustc_middle::mir::Operand;
use rustc_middle::ty::{self as mir_ty};
use rustc_span::def_id::DefId;

use super::{singleton_params, subst_singleton_params, Analyzer, ResolvedCallable};
use crate::analyze::unanalyzed_entry::{
    count_held, peel_refs, pointee, HandedOver, HandoverCount, StatedPres,
};
use crate::chc;
use crate::refine::Var;
use crate::rty::{self, ClauseBuilderExt as _, ClauseScope as _, Subtyping as _};

/// How the callee may call a closure handed over at one of its `Fn`-bounded parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Calls {
    Once,
    Repeatedly,
}

/// Whether a struct or enum of the crate in `ty` holds the closure type `closure` among its
/// type arguments: a user adapter, whose `inv` holds only where a call discharges it.
fn crate_adapter_holds<'tcx>(ty: mir_ty::Ty<'tcx>, closure: mir_ty::Ty<'tcx>) -> bool {
    ty.walk()
        .filter_map(|arg| arg.as_type())
        .any(|ty| match ty.kind() {
            mir_ty::TyKind::Adt(adt, args) => {
                adt.did().is_local() && args.types().any(|arg| closures_in(arg).contains(&closure))
            }
            _ => false,
        })
}

/// The closure types in `ty`, without repeats. A closure's own arguments (its signature, its
/// captures) are its own and not looked into: a closure it captures is called by its body.
fn closures_in(ty: mir_ty::Ty<'_>) -> Vec<mir_ty::Ty<'_>> {
    let mut closures = Vec::new();
    let mut walker = ty.walk();
    while let Some(arg) = walker.next() {
        let Some(ty) = arg.as_type() else {
            continue;
        };
        if matches!(ty.kind(), mir_ty::TyKind::Closure(..)) {
            walker.skip_current_subtree();
            if !closures.contains(&ty) {
                closures.push(ty);
            }
        }
    }
    closures
}

impl<'tcx> Analyzer<'tcx, '_> {
    /// States the obligation of each closure the call of `def_id` at `args` hands over, when the
    /// function that runs is not analyzed; `operands` are the call's arguments and `operand_tys`
    /// their types.
    pub(super) fn hand_over_closures(
        &mut self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        operands: &[Operand<'tcx>],
        operand_tys: &IndexVec<rty::FunctionParamIdx, rty::RefinedType<Var>>,
    ) {
        let ResolvedCallable::Concrete(resolved_def_id, resolved_args) =
            self.resolve_callable(def_id, args)
        else {
            return;
        };
        let contract = self
            .ctx
            .unanalyzed_contract(resolved_def_id, resolved_args)
            .or_else(|| {
                (!resolved_def_id.is_local())
                    .then(|| self.ctx.unanalyzed_contract(def_id, args))
                    .flatten()
            });
        let Some((contract_def_id, contract_args)) = contract else {
            return;
        };
        // The `pre!` stated are those of the contract the call is checked against, which is the
        // trait method's for a local impl method without its own; the bounds that let the
        // function call a closure are those of the function that runs.
        let inherited = self.ctx.inherited_contract(def_id, args, resolved_def_id);
        let (stated_def_id, stated_args) = inherited.unwrap_or((contract_def_id, contract_args));
        // A stop names the trait method, not the extern spec carrying its contract.
        let requires_of = if inherited.is_some() {
            def_id
        } else {
            contract_def_id
        };
        let stated =
            self.ctx
                .stated_pres(stated_def_id, stated_args, self.type_builder.owner_fn_id());
        for (function, function_args) in stated.functions() {
            let function = HandedOver::Function(function, function_args);
            self.record_covered(function, def_id, args);
        }
        for param in self.iterator_spec_params(contract_def_id) {
            let ty = mir_ty::EarlyBinder::bind(param.to_ty(self.tcx))
                .instantiate(self.tcx, contract_args);
            let ty = self.tcx.erase_regions(ty);
            // The iterator's `inv` states the obligation of the closures a std adapter holds in
            // the arguments at the parameters of the bounded type, not of a value of their type
            // another argument holds, whatever its type.
            let others = self.operands_not_at(contract_def_id, param, operands);
            for closure in closures_in(ty) {
                if !crate_adapter_holds(ty, closure) {
                    self.record_handover(closure, def_id, args);
                    self.record_handover_count(closure, def_id, args, others.clone(), 0);
                    continue;
                }
                // A user adapter's closure is covered only by a `pre!` the `requires` states, as
                // a `requires` of the adapter's `inv` does when `inv` states it. Otherwise it is
                // left to the walk over unanalyzed code, which stops where that code runs it: a
                // callee that only wraps the iterator (`skip`) does not.
                let operand_types = self.operand_types(operands);
                if self.states_pre_of_one(closure, &operand_types, &stated) {
                    self.record_handover(closure, def_id, args);
                    self.record_handover_count(closure, def_id, args, operand_types, 1);
                }
            }
        }
        for (param, calls) in self.fn_bounded_params(contract_def_id) {
            let ty = mir_ty::EarlyBinder::bind(param.to_ty(self.tcx))
                .instantiate(self.tcx, contract_args);
            let ty = self.tcx.erase_regions(ty);
            self.record_handover(ty, def_id, args);
            // `stated` records types, not values, so a `pre!` stated of a value of `ty` counts
            // only when the arguments hold exactly one: itself, behind references and boxes, or
            // in a field of a struct or tuple (the function of an iterator adapter), not a second
            // value of `ty`, nor one inside a collection. Otherwise each value is handed over with
            // its obligation. A type parameter here may stand for a type holding more values, so
            // the walk over unanalyzed code counts them again at each instance of the caller
            // ([`HandoverCount`]).
            let operand_types = self.operand_types(operands);
            let accounted = if self.states_pre_of_one(ty, &operand_types, &stated) {
                1
            } else {
                let holders = self.holders(ty, operands);
                for (idx, held, derefs) in &holders {
                    let handed = (contract_def_id, requires_of);
                    self.hand_over(ty, calls, &operand_tys[*idx], *held, *derefs, handed);
                }
                holders.len()
            };
            self.record_handover_count(ty, def_id, args, operand_types, accounted);
        }
    }

    /// Whether `stated` reads the `pre!` of the closure type `ty` and arguments of the types
    /// `operand_types` hold exactly one value of it, which the `pre!` is then stated of.
    fn states_pre_of_one(
        &self,
        ty: mir_ty::Ty<'tcx>,
        operand_types: &[mir_ty::Ty<'tcx>],
        stated: &StatedPres<'tcx>,
    ) -> bool {
        let count = operand_types
            .iter()
            .map(|held| count_held(self.tcx, *held, ty))
            .sum::<Option<usize>>();
        stated.names(ty) && count == Some(1)
    }

    /// Records that the call of `def_id` at `args` states the obligation of `accounted` values
    /// of the closure type `ty` held by arguments of the types `operand_types`
    /// ([`HandoverCount`]).
    fn record_handover_count(
        &mut self,
        ty: mir_ty::Ty<'tcx>,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        operand_types: Vec<mir_ty::Ty<'tcx>>,
        accounted: usize,
    ) {
        let span = self.body.basic_blocks[self.basic_block]
            .terminator()
            .source_info
            .span;
        self.ctx.record_handover_count(HandoverCount {
            owner: self.local_def_id.to_def_id(),
            callee: def_id,
            callee_args: args,
            ty,
            operand_types,
            accounted,
            span,
        });
    }

    /// The types of the arguments `operands` other than those at the parameters of
    /// `contract_def_id` whose declared type is `param`, itself or behind references and boxes;
    /// all of them for a closure or when the arguments do not match the parameters one to one.
    fn operands_not_at(
        &self,
        contract_def_id: DefId,
        param: mir_ty::ParamTy,
        operands: &[Operand<'tcx>],
    ) -> Vec<mir_ty::Ty<'tcx>> {
        let operand_types = self.operand_types(operands);
        if self.tcx.is_closure_like(contract_def_id) {
            return operand_types;
        }
        let sig = self.tcx.fn_sig(contract_def_id).instantiate_identity();
        let inputs = sig.skip_binder().inputs();
        if inputs.len() != operand_types.len() {
            return operand_types;
        }
        let param_ty = param.to_ty(self.tcx);
        operand_types
            .into_iter()
            .zip(inputs)
            .filter(|(_, declared)| peel_refs(**declared) != param_ty)
            .map(|(held, _)| held)
            .collect()
    }

    /// The types of the arguments `operands`, without regions.
    fn operand_types(&self, operands: &[Operand<'tcx>]) -> Vec<mir_ty::Ty<'tcx>> {
        operands
            .iter()
            .map(|operand| {
                self.tcx
                    .erase_regions(operand.ty(&self.local_decls, self.tcx))
            })
            .collect()
    }

    /// The arguments among `operands` that hold a value of `ty`, each with its type and the
    /// number of references and boxes that value is behind, or `None` when the argument holds it
    /// some other way (in a tuple, a struct or a collection).
    fn holders(
        &self,
        ty: mir_ty::Ty<'tcx>,
        operands: &[Operand<'tcx>],
    ) -> Vec<(rty::FunctionParamIdx, mir_ty::Ty<'tcx>, Option<usize>)> {
        let mut holders = Vec::new();
        for (idx, operand) in operands.iter().enumerate() {
            let held = self
                .tcx
                .erase_regions(operand.ty(&self.local_decls, self.tcx));
            if held.walk().any(|arg| arg.as_type() == Some(ty)) {
                let idx = rty::FunctionParamIdx::from_usize(idx);
                holders.push((idx, held, derefs_to(held, ty)));
            }
        }
        holders
    }

    /// The bounds of `contract_def_id` on its type parameters: each parameter with the trait it
    /// is bounded by.
    fn param_bounds(
        &self,
        contract_def_id: DefId,
    ) -> Vec<(mir_ty::ParamTy, mir_ty::TraitRef<'tcx>)> {
        let predicates = self
            .tcx
            .predicates_of(contract_def_id)
            .instantiate_identity(self.tcx);
        let mut bounds = Vec::new();
        for clause in predicates.predicates {
            let Some(trait_clause) = clause.as_trait_clause() else {
                continue;
            };
            let trait_ref = self
                .tcx
                .instantiate_bound_regions_with_erased(trait_clause)
                .trait_ref;
            if let mir_ty::TyKind::Param(param) = *trait_ref.self_ty().kind() {
                bounds.push((param, trait_ref));
            }
        }
        bounds
    }

    /// The type parameters of `contract_def_id` with an `Fn`, `FnMut` or `FnOnce` bound, directly
    /// or through a supertrait, and how often the bounds let the function call a value of each:
    /// repeatedly if any bound is `Fn` or `FnMut`.
    fn fn_bounded_params(&self, contract_def_id: DefId) -> Vec<(mir_ty::ParamTy, Calls)> {
        let mut params: Vec<(mir_ty::ParamTy, Calls)> = Vec::new();
        for (param, trait_ref) in self.param_bounds(contract_def_id) {
            for kind in self.fn_trait_kinds(trait_ref) {
                let calls = match kind {
                    mir_ty::ClosureKind::FnOnce => Calls::Once,
                    mir_ty::ClosureKind::Fn | mir_ty::ClosureKind::FnMut => Calls::Repeatedly,
                };
                match params.iter_mut().find(|(p, _)| *p == param) {
                    Some((_, known)) if calls == Calls::Repeatedly => *known = calls,
                    Some(_) => {}
                    None => params.push((param, calls)),
                }
            }
        }
        params
    }

    /// The type parameters of `contract_def_id` bounded by std.rs's `IteratorSpec`. A closure
    /// inside the iterator one is instantiated with (the function of a `Map`) is run by the
    /// iterator's `next`, so the call hands it over. For std's `Map` its obligation is met where
    /// the iterator was made: `map` requires `Map`'s `inv`, which states the closure's `pre!` of
    /// every item it can be called on and is kept by every `next`, the only way std.rs lets the
    /// state of a `Map` change. So it holds of every `Map` a callee receives, whether or not the
    /// callee's contract requires `inv` (a trusted consumer's need not). A user adapter's `inv`
    /// holds only where a call discharges it, so a closure a struct or enum of the crate holds is
    /// covered only when the callee's `requires` states its `pre!` of the one value of its type
    /// the arguments hold, which a `requires` of the adapter's `inv` does when `inv` states it
    /// positively; otherwise the walk over unanalyzed code stops where that code runs it.
    fn iterator_spec_params(&self, contract_def_id: DefId) -> Vec<mir_ty::ParamTy> {
        let Some(iterator_spec) = self.ctx.def_ids.iterator_spec() else {
            return Vec::new();
        };
        let mut params = Vec::new();
        for (param, trait_ref) in self.param_bounds(contract_def_id) {
            if trait_ref.def_id == iterator_spec && !params.contains(&param) {
                params.push(param);
            }
        }
        params
    }

    /// The closure traits among `trait_ref` and its supertraits.
    fn fn_trait_kinds(&self, trait_ref: mir_ty::TraitRef<'tcx>) -> Vec<mir_ty::ClosureKind> {
        let mut kinds = Vec::new();
        let mut pending = vec![trait_ref];
        let mut seen = std::collections::HashSet::new();
        while let Some(trait_ref) = pending.pop() {
            if !seen.insert(trait_ref.def_id) {
                continue;
            }
            kinds.extend(self.tcx.fn_trait_kind_from_def_id(trait_ref.def_id));
            pending.extend(crate::analyze::extern_spec::supertrait_bounds(
                self.tcx, trait_ref,
            ));
        }
        kinds
    }

    /// Records that the closure `ty` stands for is handed over at a call of `def_id` at `args`.
    fn record_handover(
        &mut self,
        ty: mir_ty::Ty<'tcx>,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) {
        let handed_over = match *peel_refs(ty).kind() {
            mir_ty::TyKind::Closure(def_id, _) => HandedOver::Closure(def_id),
            mir_ty::TyKind::Param(param) => {
                HandedOver::Param(self.type_builder.param_def_id(&param))
            }
            _ => return,
        };
        self.record_covered(handed_over, def_id, args);
    }

    /// Records that the call of `def_id` at `args` covers `covered`. The walk over unanalyzed
    /// code resolves the call at each instance of the caller.
    fn record_covered(
        &mut self,
        covered: HandedOver<'tcx>,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) {
        let owner = self.local_def_id.to_def_id();
        self.ctx.record_handover(owner, def_id, args, covered);
    }

    /// States the obligation of the value of type `ty` that an argument of type `held`, typed
    /// `operand_ty`, holds behind `derefs` references and boxes; `None` stops, as the value is
    /// held some way Thrust cannot follow. The value is handed to the function `contract_def_id`
    /// gives the contract of, and `requires_of` is the function whose contract the call is
    /// checked against, in whose `requires` a stop asks to state its `pre!`.
    fn hand_over(
        &mut self,
        ty: mir_ty::Ty<'tcx>,
        calls: Calls,
        operand_ty: &rty::RefinedType<Var>,
        held: mir_ty::Ty<'tcx>,
        derefs: Option<usize>,
        (contract_def_id, requires_of): (DefId, DefId),
    ) {
        let Some(derefs) = derefs else {
            self.tcx.dcx().span_fatal(
                self.body.basic_blocks[self.basic_block]
                    .terminator()
                    .source_info
                    .span,
                format!(
                    "a value of `{ty}` is handed to `{}`, which Thrust does not analyze, inside \
                     `{held}`, where Thrust cannot follow it: state the `pre!` it needs in the \
                     `requires` of `{}`",
                    self.tcx.def_path_str(contract_def_id),
                    self.tcx.def_path_str(requires_of),
                ),
            );
        };
        let callable = peel_refs(ty);
        let derefs = derefs + count_refs(ty);
        if let mir_ty::TyKind::FnPtr(..) = callable.kind() {
            if derefs == 0 {
                let total = rty::RefinedType::<rty::Closed>::unrefined(
                    operand_ty.ty.clone().strip_refinement(),
                );
                let clauses = self.env.relate_sub_refined_type(operand_ty, &total);
                self.ctx.extend_clauses(clauses);
                return;
            }
        }
        let Some(contract) = self.handed_over_contract(callable) else {
            self.tcx.dcx().span_fatal(
                self.body.basic_blocks[self.basic_block]
                    .terminator()
                    .source_info
                    .span,
                format!(
                    "`{callable}` is handed to `{}`, which Thrust does not analyze, and has no \
                     contract Thrust can require of it: state the `pre!` it needs in the \
                     `requires` of `{}`",
                    self.tcx.def_path_str(contract_def_id),
                    self.tcx.def_path_str(requires_of),
                ),
            );
        };
        let holder = self.env.immut_bind_tmp(operand_ty.clone());
        let state = deref_term(
            chc::Term::var(rty::RefinedTypeVar::Free(holder)),
            &operand_ty.ty,
            derefs,
        );
        let receiver = contract.params[rty::FunctionParamIdx::from_usize(0)]
            .ty
            .clone();
        let changes_state = receiver.as_pointer().is_some_and(|ptr| ptr.is_mut())
            && calls == Calls::Repeatedly
            && !receiver.to_sort().deref().is_singleton();
        let clauses = if changes_state {
            reachable_states_obligation(&mut self.env, &mut *self.ctx, &contract, holder, state)
        } else {
            once_obligation(&self.env, &contract, state)
        };
        self.ctx.extend_clauses(clauses);
    }

    /// The contract a closure value of type `callable` is called by: a closure's own, or that of
    /// the caller's closure-bounded type parameter.
    fn handed_over_contract(&mut self, callable: mir_ty::Ty<'tcx>) -> Option<rty::FunctionType> {
        match *callable.kind() {
            mir_ty::TyKind::Closure(closure_def_id, closure_args) => {
                let parent_count = self.tcx.generics_of(closure_def_id).parent_count;
                let parent_args = self.tcx.mk_args(&closure_args[..parent_count]);
                let caller = self.type_builder.owner_fn_id();
                let def_ty = self
                    .ctx
                    .def_ty_with_args(closure_def_id, parent_args, caller)?;
                def_ty.ty.as_function().cloned()
            }
            mir_ty::TyKind::Param(param) => self.type_builder.closure_param_contract(
                param,
                self.local_def_id,
                self.analysis_key.generic_args,
            ),
            _ => None,
        }
    }
}

/// The number of references and boxes around `ty`.
fn count_refs(ty: mir_ty::Ty<'_>) -> usize {
    let mut ty = ty;
    let mut count = 0;
    while let Some(inner) = pointee(ty) {
        ty = inner;
        count += 1;
    }
    count
}

/// The number of references and boxes a value of `held` is behind which is of type `ty`, or
/// `None` when `held` holds `ty` some other way.
fn derefs_to<'tcx>(mut held: mir_ty::Ty<'tcx>, ty: mir_ty::Ty<'tcx>) -> Option<usize> {
    let mut derefs = 0;
    while held != ty {
        held = pointee(held)?;
        derefs += 1;
    }
    Some(derefs)
}

/// The term of the value `derefs` pointers into `term`, a value of type `ty`.
fn deref_term<V>(mut term: chc::Term<V>, mut ty: &rty::Type<Var>, derefs: usize) -> chc::Term<V> {
    for _ in 0..derefs {
        let ptr = ty
            .as_pointer()
            .expect("a reference or box is a pointer type");
        term = ptr.kind.deref_term(term);
        ty = &ptr.elem.ty;
    }
    term
}

/// The arguments of a call of `contract` that receives the closure as `receiver` and takes any
/// logical arguments.
fn call_args<T: Clone>(
    contract: &rty::FunctionType,
    receiver: rty::Refinement<T>,
) -> IndexVec<rty::FunctionParamIdx, rty::RefinedType<T>> {
    contract
        .params
        .iter_enumerated()
        .map(|(idx, param)| {
            let ty = param.ty.clone().strip_refinement().vacuous();
            if idx.index() == 0 {
                rty::RefinedType::new(ty, receiver.clone())
            } else {
                rty::RefinedType::unrefined(ty)
            }
        })
        .collect()
}

/// The precondition of `contract` at the closure state `state` for every argument, under the
/// caller's environment: the call a verified caller makes, borrowing the closure as the
/// contract's receiver takes it, with a `&mut` receiver's final state left free.
fn once_obligation(
    env: &crate::analyze::Env,
    contract: &rty::FunctionType,
    state: chc::Term<rty::RefinedTypeVar<Var>>,
) -> Vec<chc::Clause> {
    let value = value();
    let receiver_ty = &contract.params[rty::FunctionParamIdx::from_usize(0)].ty;
    let receiver: rty::Refinement<Var> = match receiver_ty.as_pointer().map(|ptr| ptr.kind) {
        Some(rty::PointerKind::Ref(rty::RefKind::Mut)) => {
            let mut receiver: rty::Refinement<Var> = value
                .equal_to(chc::Term::mut_(
                    state,
                    chc::Term::var(rty::RefinedTypeVar::Existential(0usize.into())),
                ))
                .into();
            receiver.existentials.push(receiver_ty.to_sort().deref());
            receiver
        }
        Some(rty::PointerKind::Ref(rty::RefKind::Immut)) => {
            value.equal_to(chc::Term::box_(state)).into()
        }
        _ => value.equal_to(state).into(),
    };
    let args = call_args(contract, receiver);
    let enum_defs = rty::ClauseScope::enum_defs(env);
    super::relate_param_sub_types(
        contract.params.clone(),
        &args,
        &mut env.build_clause(),
        enum_defs,
    )
}

/// E1-E3 of the module documentation, with a fresh unknown over the closure's state for the
/// states the callee's calls reach from `state`, the state `holder` holds.
fn reachable_states_obligation(
    env: &mut crate::analyze::Env,
    ctx: &mut crate::analyze::Analyzer<'_>,
    contract: &rty::FunctionType,
    holder: Var,
    state: chc::Term<rty::RefinedTypeVar<Var>>,
) -> Vec<chc::Clause> {
    let receiver_idx = rty::FunctionParamIdx::from_usize(0);
    let state_sort = contract.params[receiver_idx].ty.to_sort().deref();
    let reached = ctx.generate_pred_var(vec![state_sort]);

    let mut clauses = env
        .build_clause()
        .with_mapped_value_var(holder)
        .head(rty::Refinement::<Var>::from(reach_atom(reached, state)));

    let receiver: rty::Refinement<rty::Closed> = reach_atom(reached, value().mut_current()).into();
    let args = call_args(contract, receiver);
    clauses.extend(super::relate_param_sub_types(
        contract.params.clone(),
        &args,
        &mut chc::ClauseBuilder::default(),
        Some(&ctx.enum_defs),
    ));

    let singletons = singleton_params(&contract.params);
    let params: IndexVec<rty::FunctionParamIdx, _> = contract
        .params
        .iter()
        .map(|param| subst_singleton_params(param.clone(), &singletons))
        .collect();
    let ret = subst_singleton_params((*contract.ret).clone(), &singletons);
    let mut builder = chc::ClauseBuilder::default();
    for (idx, param) in params.iter_enumerated() {
        let sort = param.ty.to_sort();
        if !sort.is_singleton() {
            builder.add_mapped_var(idx, sort);
        }
    }
    builder.with_mapped_value_var(receiver_idx).add_body(
        rty::Refinement::<rty::FunctionParamIdx>::from(reach_atom(reached, value().mut_current())),
    );
    for (idx, param) in params.iter_enumerated() {
        if singletons.contains_key(&idx) {
            builder.with_value_var(&param.ty).add_body(param.formula());
        } else {
            builder.with_mapped_value_var(idx).add_body(param.formula());
        }
    }
    builder.with_value_var(&ret.ty).add_body(ret.formula());
    clauses.extend(
        builder.with_mapped_value_var(receiver_idx).head(
            rty::Refinement::<rty::FunctionParamIdx>::from(reach_atom(
                reached,
                value().mut_final(),
            )),
        ),
    );
    clauses
}

/// The value variable of a refinement.
fn value<T>() -> chc::Term<rty::RefinedTypeVar<T>> {
    chc::Term::var(rty::RefinedTypeVar::Value)
}

/// `reached` applied to `term`.
fn reach_atom<V>(reached: chc::PredVarId, term: chc::Term<V>) -> chc::Atom<V> {
    chc::Atom::new(reached.into(), vec![term])
}
