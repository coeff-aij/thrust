//! Trait objects (`&dyn Tr`, `&mut dyn Tr`, `Box<dyn Tr>`).
//!
//! A trait object is an existential package, `∃T. T` with `T: Tr` and the impl's vtable as the
//! dictionary (Mitchell and Plotkin; Läufer). Its model is opaque: the unsize coercion packs a
//! value into a fresh opaque one and checks every vtable method of the impl against the trait's
//! contract, and a call through the vtable takes the trait's contract at `Self = dyn Tr`. That
//! contract holds of every impl the call may reach when it does not mention `self` or `Self`,
//! whose model the opaque value does not have; a contract that does is rejected at the call.

use rustc_middle::mir::Operand;
use rustc_middle::ty::{self as mir_ty};
use rustc_span::def_id::DefId;

use super::Analyzer;
use crate::analyze;
use crate::chc;
use crate::refine::{PlaceType, PlaceTypeBuilder};

/// The type a pointer type (`&T`, `&mut T`, `Box<T>`) points to.
fn pointee<'tcx>(ty: mir_ty::Ty<'tcx>) -> Option<mir_ty::Ty<'tcx>> {
    ty.builtin_deref(true).or_else(|| ty.boxed_ty())
}

/// The trait object `ty` points to, if it is a pointer to one.
pub(super) fn dyn_pointee<'tcx>(ty: mir_ty::Ty<'tcx>) -> Option<mir_ty::Ty<'tcx>> {
    pointee(ty).filter(|ty| ty.is_trait())
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    /// `operand` coerced to `ty`, a pointer to the trait object `dyn_ty`: a fresh opaque value.
    /// The operand is moved, so a `&mut` operand's prophecy stays unresolved and the lender's
    /// value after the borrow is unknown, as after a call that leaves it unconstrained.
    pub(super) fn unsize_to_dyn(
        &mut self,
        operand: Operand<'tcx>,
        ty: mir_ty::Ty<'tcx>,
        dyn_ty: mir_ty::Ty<'tcx>,
    ) -> PlaceType {
        let source_ty = operand.ty(&self.local_decls, self.tcx);
        let hidden_ty = pointee(source_ty).expect("unsize cast from a pointer");
        self.check_vtable_methods(hidden_ty, dyn_ty);
        let expected_ty = self.type_builder.build(ty).vacuous().ty;
        let mut builder = PlaceTypeBuilder::default();
        let _ = builder.subsume(self.operand_type(operand));
        let term = if expected_ty.is_mut() {
            chc::Term::mut_(chc::Term::null(), chc::Term::null())
        } else {
            chc::Term::box_(chc::Term::null())
        };
        builder.build(expected_ty, term)
    }

    /// Requests the type of each method of `hidden_ty`'s impl of `dyn_ty`'s trait and its
    /// supertraits that a call through the vtable may reach with a contract, so that its body is
    /// checked against the trait's contract.
    fn check_vtable_methods(&mut self, hidden_ty: mir_ty::Ty<'tcx>, dyn_ty: mir_ty::Ty<'tcx>) {
        let owner = self.type_builder.owner_fn_id();
        if hidden_ty.is_trait() {
            self.tcx.dcx().fatal(format!(
                "a trait object coerced to another (`{hidden_ty}` to `{dyn_ty}` in `{}`) is not \
                 supported",
                self.tcx.def_path_str(owner),
            ));
        }
        let mir_ty::TyKind::Dynamic(preds, ..) = dyn_ty.kind() else {
            unreachable!("not a trait object: {dyn_ty:?}");
        };
        let Some(principal) = preds.principal() else {
            return;
        };
        let trait_ref = self
            .tcx
            .instantiate_bound_regions_with_erased(principal.with_self_ty(self.tcx, hidden_ty));
        let mut pending = vec![trait_ref];
        let mut seen = std::collections::HashSet::new();
        while let Some(trait_ref) = pending.pop() {
            if !seen.insert(trait_ref.def_id) {
                continue;
            }
            self.check_dyn_trait(trait_ref.def_id, dyn_ty);
            for method in self
                .tcx
                .associated_items(trait_ref.def_id)
                .in_definition_order()
            {
                if !method.is_fn()
                    || !rustc_trait_selection::traits::is_vtable_safe_method(
                        self.tcx,
                        trait_ref.def_id,
                        *method,
                    )
                    || self.ctx.contract_spec_def_ids(method.def_id).is_none()
                {
                    continue;
                }
                let args = mir_ty::GenericArgs::for_item(self.tcx, method.def_id, |param, _| {
                    trait_ref
                        .args
                        .get(param.index as usize)
                        .copied()
                        .unwrap_or_else(|| self.tcx.lifetimes.re_erased.into())
                });
                self.check_vtable_impl(method.def_id, args, dyn_ty);
                let _ = self.callable_ty(method.def_id, args);
            }
            pending.extend(analyze::extern_spec::supertrait_bounds(self.tcx, trait_ref));
        }
    }

    /// Stops unless the method `def_id` at `args` resolves to a body Thrust checks against the
    /// trait's contract: an impl method of the crate that is not ignored, or the trait's default.
    fn check_vtable_impl(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        dyn_ty: mir_ty::Ty<'tcx>,
    ) {
        let instance = mir_ty::Instance::try_resolve(self.tcx, self.typing_env, def_id, args)
            .ok()
            .flatten();
        let Some(instance) = instance else {
            return;
        };
        let resolved = instance.def_id();
        if analyze::is_ignored_crate_fn(self.tcx, resolved) {
            analyze::fatal_ignored_call(self.tcx, resolved, instance.args);
        }
        if !resolved.is_local() {
            self.tcx.dcx().fatal(format!(
                "`{}` makes a `{dyn_ty}` whose `{}` is `{}` of another crate, which is not checked \
                 against the trait's contract",
                self.tcx.def_path_str(self.type_builder.owner_fn_id()),
                self.tcx.def_path_str(def_id),
                self.tcx.def_path_str_with_args(resolved, instance.args),
            ));
        }
    }

    /// Stops unless the trait `trait_def_id`, reached through the trait object `dyn_ty`, is a
    /// trait of the crate other than the closure traits that declares no law, logic function or
    /// predicate: those would be assumed of `dyn_ty`, which no impl proves them of (Creusot's
    /// `unsound_dyn`).
    fn check_dyn_trait(&self, trait_def_id: DefId, dyn_ty: mir_ty::Ty<'tcx>) {
        let tcx = self.tcx;
        let owner = tcx.def_path_str(self.type_builder.owner_fn_id());
        let trait_name = tcx.def_path_str(trait_def_id);
        if tcx.fn_trait_kind_from_def_id(trait_def_id).is_some() || !trait_def_id.is_local() {
            tcx.dcx().fatal(format!(
                "`{dyn_ty}` in `{owner}`: trait objects are supported only of the crate's own \
                 traits, and `{trait_name}` is not one"
            ));
        }
        let logic_paths = [
            analyze::annot::law_path(),
            analyze::annot::logic_path(),
            analyze::annot::predicate_path(),
        ];
        let logic_item = tcx
            .associated_items(trait_def_id)
            .in_definition_order()
            .find(|item| {
                logic_paths
                    .iter()
                    .any(|path| tcx.get_attrs_by_path(item.def_id, path).next().is_some())
            });
        if let Some(item) = logic_item {
            tcx.dcx().fatal(format!(
                "`{dyn_ty}` in `{owner}`: trait objects of a trait with laws, logic functions or \
                 predicates are not supported, and `{trait_name}` declares `{}`",
                tcx.def_path_str(item.def_id),
            ));
        }
    }

    /// Stops at a call of the trait method `def_id` through the trait object `args[0]` unless
    /// the trait gives the method a contract that does not mention `self` or `Self`.
    pub(super) fn check_dyn_call(&self, def_id: DefId, args: mir_ty::GenericArgsRef<'tcx>) {
        let tcx = self.tcx;
        let dyn_ty = args.type_at(0);
        let trait_def_id = tcx.trait_of_assoc(def_id).expect("a trait method");
        self.check_dyn_trait(trait_def_id, dyn_ty);
        let owner = tcx.def_path_str(self.type_builder.owner_fn_id());
        let method = tcx.def_path_str(def_id);
        let Some(specs) = self.ctx.contract_spec_def_ids(def_id) else {
            tcx.dcx().fatal(format!(
                "`{method}` is called through `{dyn_ty}` in `{owner}`, but has no contract on the \
                 trait: a call through a trait object takes the trait's contract"
            ));
        };
        if specs
            .into_iter()
            .any(|spec| self.ctx.contract_names_self(spec))
        {
            tcx.dcx().fatal(format!(
                "`{method}` is called through `{dyn_ty}` in `{owner}`, but its contract mentions \
                 `self` or `Self`, whose model a trait object does not have"
            ));
        }
    }

    /// Stops at a call that instantiates a type parameter with a trait object (`g::<dyn Tr>`):
    /// the callee's contract and the laws of its bounds would be assumed of `dyn Tr`.
    pub(super) fn check_no_dyn_type_arg(&self, def_id: DefId, args: mir_ty::GenericArgsRef<'tcx>) {
        let Some(dyn_ty) = args.types().find(|ty| ty.is_trait()) else {
            return;
        };
        self.tcx.dcx().fatal(format!(
            "`{}` in `{}` instantiates a type parameter with the trait object `{dyn_ty}`, which is \
             not supported",
            self.tcx.def_path_str_with_args(def_id, args),
            self.tcx.def_path_str(self.type_builder.owner_fn_id()),
        ));
    }
}
