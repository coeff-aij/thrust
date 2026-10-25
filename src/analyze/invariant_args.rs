//! Where a type with an invariant (std.rs's `Invariant`) meets code whose contract was not
//! established at it.
//!
//! The invariant is conjoined to a contract at the positions where the signature has the type
//! (`local_def::Analyzer::conjoin_type_invariants`), read on the signature at the instance. A
//! contract established over type parameters has no conjunct where it has a type parameter. In a
//! crate with an `Invariant` impl every generic body is therefore analyzed at each instance
//! ([`analyze::Analyzer::per_instance_generics`]); what is left is code Thrust does not analyze,
//! which is rejected at an instance that holds such a type.

use std::collections::HashSet;

use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;

use crate::analyze;

impl<'tcx> analyze::Analyzer<'tcx> {
    /// The impl item of std.rs's `Invariant::invariant` at `ty` in `owner_fn_id`'s environment:
    /// `ty`'s invariant, which contracts conjoin. `None` when no impl resolves, and for a type
    /// whose values have one model (a singleton sort), whose invariant is left out.
    pub fn type_invariant_instance(
        &self,
        ty: mir_ty::Ty<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<mir_ty::Instance<'tcx>> {
        use mir_ty::TypeVisitableExt as _;
        let inv_did = self.crate_type_invariant()?;
        if ty.has_escaping_bound_vars() {
            return None;
        }
        let typing_env =
            analyze::predicate_typing_env(self.tcx, owner_fn_id, self.def_ids().model_ty());
        let args = self.tcx.mk_args(&[ty.into()]);
        let instance = mir_ty::Instance::try_resolve(self.tcx, typing_env, inv_did, args)
            .ok()
            .flatten()
            .filter(|instance| instance.def_id() != inv_did)?;
        let singleton = self
            .type_builder(self.def_ids(), owner_fn_id)
            .build(ty)
            .to_sort()
            .is_singleton();
        (!singleton).then_some(instance)
    }

    /// The `invariant` predicate of std.rs's `Invariant`, when an impl of it exists in the crate.
    pub(super) fn crate_type_invariant(&self) -> Option<DefId> {
        let trait_did = self.def_ids().type_invariant()?;
        self.tcx.all_impls(trait_did).next()?;
        invariant_pred(self.tcx, trait_did)
    }

    /// A type with an invariant ([`Self::type_invariant_instance`]) that `roots` hold once
    /// normalized (which reveals opaque types): one of them, or a type among their generic
    /// arguments, references, tuples, arrays, slices, function pointers, and the signatures of
    /// function items and closures, whose results reach a trait method through
    /// `FnOnce::Output`. A closure's captures and an ADT's fields are not looked into.
    fn invariant_type_in(
        &self,
        roots: impl IntoIterator<Item = mir_ty::Ty<'tcx>>,
        owner_fn_id: DefId,
    ) -> Option<mir_ty::Ty<'tcx>> {
        let tcx = self.tcx;
        self.crate_type_invariant()?;
        let typing_env = analyze::predicate_typing_env(tcx, owner_fn_id, self.def_ids().model_ty());
        let normalize = |ty: mir_ty::Ty<'tcx>| {
            let ty = tcx.erase_regions(ty);
            tcx.try_normalize_erasing_regions(typing_env, ty)
                .unwrap_or(ty)
        };
        let mut pending: Vec<_> = roots.into_iter().map(normalize).collect();
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
                if self.type_invariant_instance(ty, owner_fn_id).is_some() {
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

    /// Stops when `def_id`, a generic function whose body Thrust does not analyze at `args` (std
    /// code, a trusted function, a derived method), is used there by `caller_def_id` through its
    /// contract while its type arguments or its signature at them hold a type with an invariant:
    /// the contract was established over its type parameters, where it has no conjunct of that
    /// invariant, and the code may run that type's impls on values nobody checked.
    pub fn stop_unanalyzed_at_invariant(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) {
        if args.types().next().is_none() {
            return;
        }
        let sig = self.tcx.fn_sig(def_id).instantiate(self.tcx, args);
        let sig = self.tcx.instantiate_bound_regions_with_erased(sig);
        let roots = args.types().chain(sig.inputs_and_output.iter());
        let Some(ty) = self.invariant_type_in(roots, caller_def_id) else {
            return;
        };
        self.tcx.dcx().fatal(format!(
            "`{}`, which Thrust does not analyze, is used in `{}` at `{ty}`, which has an \
             invariant: call it at types without one, or through a function of the crate \
             whose contract states what it keeps",
            self.tcx.def_path_str_with_args(def_id, args),
            self.tcx.def_path_str(caller_def_id),
        ))
    }

    /// Stops at a generic def's contract reused at an instance that holds a type with an
    /// invariant, which no body analyzed there has checked.
    pub fn stop_reused_at_invariant(&self) {
        let reused = self.reused_generic_instances.borrow().clone();
        for (def_id, args, caller_def_id) in reused {
            self.stop_unanalyzed_at_invariant(def_id, args, caller_def_id);
        }
    }

    /// Stops when an associated type of a trait impl of the crate, other than a model type,
    /// holds a type with an invariant. Code Thrust does not analyze, generic over a type whose
    /// impl binds it, reads its values through the projection and may pass them to that type's
    /// impls, while neither its type arguments nor its signature show the type.
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
            if let Some(inv_ty) = self.invariant_type_in([ty], self.tcx.parent(def_id)) {
                self.tcx.dcx().span_fatal(
                    self.tcx.def_span(def_id),
                    format!(
                        "the associated type `{}` holds `{inv_ty}`, which has an invariant: code \
                         Thrust does not analyze could read it through the projection",
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
