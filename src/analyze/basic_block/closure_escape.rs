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
use crate::analyze::unanalyzed_entry::HandedOver;
use crate::analyze::TypeParam;
use crate::chc;
use crate::refine::Var;
use crate::rty::{self, ClauseBuilderExt as _, ClauseScope as _, Subtyping as _};

/// How the callee may call a closure handed over at one of its `Fn`-bounded parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Calls {
    Once,
    Repeatedly,
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
        let stated = self.ctx.stated_pres(contract_def_id);
        for (param, calls) in self.fn_bounded_params(contract_def_id) {
            let ty = mir_ty::EarlyBinder::bind(param.to_ty(self.tcx))
                .instantiate(self.tcx, contract_args);
            let ty = self.tcx.erase_regions(ty);
            self.record_handover(ty, def_id, resolved_def_id);
            if stated.names_param(param.name) {
                continue;
            }
            for (idx, operand) in operands.iter().enumerate() {
                let idx = rty::FunctionParamIdx::from_usize(idx);
                self.hand_over(ty, calls, operand, &operand_tys[idx], contract_def_id);
            }
        }
    }

    /// The type parameters of `contract_def_id` with an `Fn`, `FnMut` or `FnOnce` bound, and how
    /// often the bound lets the function call a value of each.
    fn fn_bounded_params(&self, contract_def_id: DefId) -> Vec<(mir_ty::ParamTy, Calls)> {
        let mut params: Vec<(mir_ty::ParamTy, Calls)> = Vec::new();
        let predicates = self
            .tcx
            .predicates_of(contract_def_id)
            .instantiate_identity(self.tcx);
        for clause in predicates.predicates {
            let Some(trait_clause) = clause.as_trait_clause() else {
                continue;
            };
            let trait_ref = trait_clause.skip_binder().trait_ref;
            let Some(kind) = self.tcx.fn_trait_kind_from_def_id(trait_ref.def_id) else {
                continue;
            };
            let mir_ty::TyKind::Param(param) = *trait_ref.self_ty().kind() else {
                continue;
            };
            if params.iter().any(|(p, _)| *p == param) {
                continue;
            }
            let calls = match kind {
                mir_ty::ClosureKind::FnOnce => Calls::Once,
                mir_ty::ClosureKind::Fn | mir_ty::ClosureKind::FnMut => Calls::Repeatedly,
            };
            params.push((param, calls));
        }
        params
    }

    /// Records that the closure `ty` stands for is handed over at a call of `def_id`, which
    /// resolves to `resolved_def_id`.
    fn record_handover(&mut self, ty: mir_ty::Ty<'tcx>, def_id: DefId, resolved_def_id: DefId) {
        let owner = self.local_def_id.to_def_id();
        let handed_over = match *peel_refs(ty).kind() {
            mir_ty::TyKind::Closure(def_id, _) => HandedOver::Closure(def_id),
            mir_ty::TyKind::Param(param) => {
                HandedOver::Param(self.type_builder.param_def_id(&param))
            }
            _ => return,
        };
        self.ctx.record_handover(owner, def_id, handed_over);
        if resolved_def_id != def_id {
            self.ctx
                .record_handover(owner, resolved_def_id, handed_over);
        }
    }

    /// States the obligation of the value of type `ty` that `operand` holds, if it holds one.
    fn hand_over(
        &mut self,
        ty: mir_ty::Ty<'tcx>,
        calls: Calls,
        operand: &Operand<'tcx>,
        operand_ty: &rty::RefinedType<Var>,
        contract_def_id: DefId,
    ) {
        let held = self
            .tcx
            .erase_regions(operand.ty(&self.local_decls, self.tcx));
        if !held.walk().any(|arg| arg.as_type() == Some(ty)) {
            return;
        }
        let Some(derefs) = derefs_to(held, ty) else {
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
                    self.tcx.def_path_str(contract_def_id),
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
                    self.tcx.def_path_str(contract_def_id),
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
            mir_ty::TyKind::Param(param) => {
                let type_param = TypeParam::GenericType {
                    param_def_id: self.type_builder.param_def_id(&param),
                    local_idx: self.type_builder.param_local_idx(&param),
                };
                if let Some(contract) = self.ctx.get_closure_type(type_param.clone()) {
                    return Some(contract);
                }
                let contract = self.type_builder.build_closure_type_for_param(
                    param,
                    self.local_def_id,
                    self.tcx.mk_args(&[]),
                )?;
                self.type_builder
                    .register_closure_type_param(type_param, contract.clone());
                Some(contract)
            }
            _ => None,
        }
    }
}

/// `ty` without the references around it.
fn peel_refs(mut ty: mir_ty::Ty<'_>) -> mir_ty::Ty<'_> {
    while let mir_ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    ty
}

/// The number of references around `ty`.
fn count_refs(mut ty: mir_ty::Ty<'_>) -> usize {
    let mut count = 0;
    while let mir_ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
        count += 1;
    }
    count
}

/// The number of references and boxes a value of `held` is behind which is of type `ty`, or
/// `None` when `held` holds `ty` some other way.
fn derefs_to<'tcx>(mut held: mir_ty::Ty<'tcx>, ty: mir_ty::Ty<'tcx>) -> Option<usize> {
    let mut derefs = 0;
    while held != ty {
        held = match held.kind() {
            mir_ty::TyKind::Ref(_, inner, _) => *inner,
            mir_ty::TyKind::Adt(adt, args) if adt.is_box() => args.type_at(0),
            _ => return None,
        };
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
    super::relate_param_sub_types(contract.params.clone(), &args, &mut env.build_clause())
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
