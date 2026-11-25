//! What an analyzed call into code Thrust does not analyze covers
//! ([`crate::analyze::unanalyzed_entry`]).
//!
//! The callee's `requires` states the `pre!` of the functions and closures the callee runs, and
//! the caller discharges it. A function whose `pre!` it states is recorded, so that the walk over
//! the unanalyzed code does not require that function to accept every argument where the call
//! leads. A closure is required nothing more: a contract states the `pre!` of every closure call
//! it makes, as Creusot's do. A function pointer handed over at an `Fn`-bounded parameter whose
//! `pre!` the `requires` does not state is a function reified, which the walk does not see called,
//! so it must accept every argument, as a function entered from such code must.

use rustc_index::IndexVec;
use rustc_middle::mir::Operand;
use rustc_middle::ty::{self as mir_ty};
use rustc_span::def_id::DefId;

use super::{Analyzer, ResolvedCallable};
use crate::analyze::unanalyzed_entry::{peel_refs, pointee, StatedFunctionPre};
use crate::refine::Var;
use crate::rty::{self, Subtyping as _};

impl<'tcx> Analyzer<'tcx, '_> {
    /// Records the functions whose `pre!` the contract of the call of `def_id` at `args` states,
    /// and requires each function pointer handed over at a parameter bounded by `Fn`, `FnMut` or
    /// `FnOnce` to accept every argument, when the function that
    /// runs is not analyzed; `operands` are the call's arguments and `operand_tys` their types.
    pub(super) fn cover_unanalyzed_call(
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
        // function call a value are those of the function that runs.
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
            self.ctx.record_stated_function_pre(StatedFunctionPre {
                owner: self.local_def_id.to_def_id(),
                callee: def_id,
                callee_args: args,
                function,
                function_args,
            });
        }
        for param in self.fn_bounded_params(contract_def_id) {
            let ty = mir_ty::EarlyBinder::bind(param.to_ty(self.tcx))
                .instantiate(self.tcx, contract_args);
            let ty = self.tcx.erase_regions(ty);
            if !matches!(peel_refs(ty).kind(), mir_ty::TyKind::FnPtr(..)) {
                continue;
            }
            for (idx, held, derefs) in self.holders(ty, operands) {
                let handed = (contract_def_id, requires_of);
                self.require_fn_ptr_accepts_every_argument(
                    ty,
                    &operand_tys[idx],
                    held,
                    derefs,
                    handed,
                );
            }
        }
    }

    /// The type of `operand`, without regions.
    fn operand_ty(&self, operand: &Operand<'tcx>) -> mir_ty::Ty<'tcx> {
        self.tcx
            .erase_regions(operand.ty(&self.local_decls, self.tcx))
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
            let held = self.operand_ty(operand);
            if held.walk().any(|arg| arg.as_type() == Some(ty)) {
                let idx = rty::FunctionParamIdx::from_usize(idx);
                holders.push((idx, held, derefs_to(held, ty)));
            }
        }
        holders
    }

    /// The type parameters of `contract_def_id` with an `Fn`, `FnMut` or `FnOnce` bound,
    /// directly or through a supertrait.
    fn fn_bounded_params(&self, contract_def_id: DefId) -> Vec<mir_ty::ParamTy> {
        let predicates = self
            .tcx
            .predicates_of(contract_def_id)
            .instantiate_identity(self.tcx);
        let mut params = Vec::new();
        for clause in predicates.predicates {
            let Some(trait_clause) = clause.as_trait_clause() else {
                continue;
            };
            let trait_ref = self
                .tcx
                .instantiate_bound_regions_with_erased(trait_clause)
                .trait_ref;
            let mir_ty::TyKind::Param(param) = *trait_ref.self_ty().kind() else {
                continue;
            };
            if self.has_fn_trait(trait_ref) && !params.contains(&param) {
                params.push(param);
            }
        }
        params
    }

    /// Whether `trait_ref` or one of its supertraits is a closure trait.
    fn has_fn_trait(&self, trait_ref: mir_ty::TraitRef<'tcx>) -> bool {
        let mut pending = vec![trait_ref];
        let mut seen = std::collections::HashSet::new();
        while let Some(trait_ref) = pending.pop() {
            if !seen.insert(trait_ref.def_id) {
                continue;
            }
            if self
                .tcx
                .fn_trait_kind_from_def_id(trait_ref.def_id)
                .is_some()
            {
                return true;
            }
            pending.extend(crate::analyze::extern_spec::supertrait_bounds(
                self.tcx, trait_ref,
            ));
        }
        false
    }

    /// Requires the function pointer of type `ty` that an argument of type `held`, typed
    /// `operand_ty`, holds behind `derefs` references and boxes to accept every argument; `None`
    /// stops, as the value is held some way Thrust cannot follow, and so does a pointer behind a
    /// reference or a box, which has no contract Thrust can require of it. The value is handed to
    /// the function `contract_def_id` gives the contract of, and `requires_of` is the function
    /// whose contract the call is checked against, which a stop names.
    fn require_fn_ptr_accepts_every_argument(
        &mut self,
        ty: mir_ty::Ty<'tcx>,
        operand_ty: &rty::RefinedType<Var>,
        held: mir_ty::Ty<'tcx>,
        derefs: Option<usize>,
        (contract_def_id, requires_of): (DefId, DefId),
    ) {
        let span = self.body.basic_blocks[self.basic_block]
            .terminator()
            .source_info
            .span;
        let Some(derefs) = derefs else {
            self.tcx.dcx().span_fatal(
                span,
                format!(
                    "a value of `{ty}` is handed to `{}`, which Thrust does not analyze, inside \
                     `{held}`, where Thrust cannot follow it: pass a function item or a closure \
                     instead, or give `{}` a contract that does not call it",
                    self.tcx.def_path_str(contract_def_id),
                    self.tcx.def_path_str(requires_of),
                ),
            );
        };
        if derefs + count_refs(ty) != 0 {
            self.tcx.dcx().span_fatal(
                span,
                format!(
                    "`{}` is handed to `{}`, which Thrust does not analyze, and has no contract \
                     Thrust can require of it: pass a function item or a closure instead, or give \
                     `{}` a contract that does not call it",
                    peel_refs(ty),
                    self.tcx.def_path_str(contract_def_id),
                    self.tcx.def_path_str(requires_of),
                ),
            );
        }
        let total =
            rty::RefinedType::<rty::Closed>::unrefined(operand_ty.ty.clone().strip_refinement());
        let clauses = self.env.relate_sub_refined_type(operand_ty, &total);
        self.ctx.extend_clauses(clauses);
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
