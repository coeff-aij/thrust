//! Type arguments that contain a type with an invariant (std.rs's `Invariant`).
//!
//! The invariant is conjoined to a contract at the positions where the signature has the type
//! (`local_def::Analyzer::conjoin_type_invariants`), read on the signature at the instance. A
//! contract established at type parameters, by a body verified once over them or by code Thrust
//! does not analyze, has no conjunct where it has a type parameter, so it is not the contract
//! at arguments that contain such a type. Code that runs at those arguments is therefore analyzed
//! at them, or rejected.

use std::collections::HashSet;

use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;

use crate::analyze;

impl<'tcx> analyze::Analyzer<'tcx> {
    /// A type with an `Invariant` impl that `args`, read in `owner_fn_id`'s environment, contain
    /// once normalized (which reveals opaque types): one of them, or a type among their generic
    /// arguments, references, tuples, arrays, slices, function pointers, and the signatures of
    /// function items and closures, whose results reach a trait method through
    /// `FnOnce::Output`. A closure's captures and an ADT's fields are not looked into. `None` in
    /// a crate without an `Invariant` impl.
    pub fn invariant_type_in(
        &self,
        args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<mir_ty::Ty<'tcx>> {
        let tcx = self.tcx;
        let inv_did = self.crate_type_invariant()?;
        let typing_env = analyze::predicate_typing_env(tcx, owner_fn_id, self.def_ids().model_ty());
        let normalize = |ty: mir_ty::Ty<'tcx>| {
            let ty = tcx.erase_regions(ty);
            tcx.try_normalize_erasing_regions(typing_env, ty)
                .unwrap_or(ty)
        };
        let mut pending: Vec<_> = args.types().map(normalize).collect();
        let mut seen = HashSet::new();
        while let Some(root) = pending.pop() {
            let mut walker = root.walk();
            while let Some(arg) = walker.next() {
                let Some(ty) = arg.as_type() else {
                    continue;
                };
                if !seen.insert(ty) {
                    walker.skip_current_subtree();
                    continue;
                }
                if has_invariant_impl(tcx, typing_env, inv_did, ty) {
                    return Some(ty);
                }
                match ty.kind() {
                    mir_ty::TyKind::Closure(_, closure_args) => {
                        walker.skip_current_subtree();
                        let closure = closure_args.as_closure();
                        pending.extend(closure.parent_args().iter().filter_map(|a| a.as_type()));
                        pending.push(normalize(closure.sig_as_fn_ptr_ty()));
                    }
                    mir_ty::TyKind::FnDef(def_id, fn_args) => {
                        let sig = tcx.fn_sig(*def_id).instantiate(tcx, fn_args);
                        let sig = tcx.instantiate_bound_regions_with_erased(sig);
                        pending.extend(sig.inputs_and_output.iter().map(normalize));
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// The `invariant` predicate of std.rs's `Invariant`, when an impl of it exists in the crate.
    fn crate_type_invariant(&self) -> Option<DefId> {
        let trait_did = self.def_ids().type_invariant()?;
        self.tcx.all_impls(trait_did).next()?;
        invariant_pred(self.tcx, trait_did)
    }

    /// Stops when the instance `def_id` at `args`, used by `caller_def_id` through its contract,
    /// is code that Thrust does not analyze at those arguments while they contain a type with an
    /// invariant.
    pub fn stop_unanalyzed_at_invariant(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) {
        let Some(ty) = self.invariant_type_in(args, caller_def_id) else {
            return;
        };
        self.tcx.dcx().fatal(format!(
            "`{}`, used in `{}`, runs at `{ty}`, a type with an invariant, but its contract was \
             not checked against a body analyzed there: code Thrust does not analyze (std, a \
             trusted function), and a generic function reused at its own instance, cannot be \
             used at a type argument that contains a type with an invariant",
            self.tcx.def_path_str_with_args(def_id, args),
            self.tcx.def_path_str(caller_def_id),
        ))
    }

    /// Stops at a generic def's contract reused at a type argument with an invariant, which no
    /// body analyzed there has checked. A trait method's trait-level contract is not one: the
    /// call resolves to an impl, whose own instance is checked.
    pub fn stop_reused_at_invariant(&self) {
        let reused = self.reused_generic_instances.borrow().clone();
        for (def_id, args, caller_def_id) in reused {
            if self.tcx.trait_of_assoc(def_id).is_none() {
                self.stop_unanalyzed_at_invariant(def_id, args, caller_def_id);
            }
        }
    }

    /// Stops when an associated type of a trait impl of the crate, other than a model type,
    /// contains a type with an invariant: a generic body that reads the associated type through a type parameter would
    /// pass its values to that type's impls without the invariant.
    pub fn check_associated_types_without_invariant(&self) {
        if self.crate_type_invariant().is_none() {
            return;
        }
        for item_id in self.tcx.hir_crate_items(()).impl_items() {
            let def_id = item_id.owner_id.to_def_id();
            if self.tcx.def_kind(def_id) != rustc_hir::def::DefKind::AssocTy {
                continue;
            }
            // A model type is a type of the logic, of which executable code holds no value.
            let trait_item = self.tcx.associated_item(def_id).trait_item_def_id;
            if trait_item.is_some() && trait_item == self.def_ids().model_ty() {
                continue;
            }
            let ty = self.tcx.type_of(def_id).instantiate_identity();
            let args = self.tcx.mk_args(&[ty.into()]);
            if let Some(inv_ty) = self.invariant_type_in(args, self.tcx.parent(def_id)) {
                self.tcx.dcx().span_fatal(
                    self.tcx.def_span(def_id),
                    format!(
                        "the associated type `{}` contains `{inv_ty}`, a type with an invariant, \
                         which a generic function reading it through a type parameter would not \
                         require",
                        self.tcx.def_path_str(def_id),
                    ),
                );
            }
        }
    }
}

fn invariant_pred(tcx: TyCtxt<'_>, trait_did: DefId) -> Option<DefId> {
    Some(
        tcx.associated_items(trait_did)
            .filter_by_name_unhygienic(rustc_span::Symbol::intern("invariant"))
            .next()?
            .def_id,
    )
}

fn has_invariant_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    inv_did: DefId,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    use mir_ty::TypeVisitableExt as _;
    if ty.has_escaping_bound_vars() {
        return false;
    }
    let args = tcx.mk_args(&[ty.into()]);
    matches!(
        mir_ty::Instance::try_resolve(tcx, typing_env, inv_did, args),
        Ok(Some(instance)) if instance.def_id() != inv_did
    )
}
