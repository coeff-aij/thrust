//! Trait objects (`&dyn Tr`, `&mut dyn Tr`, `Box<dyn Tr>`).
//!
//! A trait object is an existential package, `∃T. T` with `T: Tr` and the impl's vtable as the
//! dictionary (Mitchell and Plotkin; Läufer). Its model is opaque: the unsize coercion packs a
//! value into a fresh opaque one, requires the value's type invariant, and checks every vtable
//! method of the impl against the trait's contract, and a call through the vtable takes the
//! trait's contract at `Self = dyn Tr`. That contract holds of every impl the call may reach,
//! under the invariant checked at packing, when it does not mention `self` or `Self`, whose model
//! the opaque value does not have; a contract that does is rejected at the call.

use rustc_middle::mir::Operand;
use rustc_middle::ty::{self as mir_ty};
use rustc_span::def_id::DefId;

use super::Analyzer;
use crate::analyze;
use crate::chc;
use crate::refine::{PlaceType, PlaceTypeBuilder, Var};
use crate::rty::{self, Subtyping as _};

/// The type a pointer type (`&T`, `&mut T`, `Box<T>`) points to.
fn pointee<'tcx>(ty: mir_ty::Ty<'tcx>) -> Option<mir_ty::Ty<'tcx>> {
    ty.builtin_deref(true).or_else(|| ty.boxed_ty())
}

/// The trait object `ty` points to, if it is a pointer to one.
pub(super) fn dyn_pointee<'tcx>(ty: mir_ty::Ty<'tcx>) -> Option<mir_ty::Ty<'tcx>> {
    pointee(ty).filter(|ty| ty.is_trait())
}

/// Stops at an unsize coercion to `ty` that makes a trait object other than `&dyn Tr`,
/// `&mut dyn Tr` or `Box<dyn Tr>` (`Rc<dyn Tr>`, a `CoerceUnsized` struct), which would skip the
/// checks of the coercion.
pub(super) fn fatal_unsupported_unsize<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    ty: mir_ty::Ty<'tcx>,
    owner: DefId,
) {
    let makes_dyn = ty
        .walk()
        .any(|arg| matches!(arg.kind(), mir_ty::GenericArgKind::Type(ty) if ty.is_trait()));
    if makes_dyn {
        tcx.dcx().fatal(format!(
            "a coercion to `{ty}` in `{}` is not supported: trait objects are made only as \
             `&dyn`, `&mut dyn` or `Box<dyn>`",
            tcx.def_path_str(owner),
        ));
    }
}

/// The principal trait of the trait object `ty`.
fn principal_def_id(ty: mir_ty::Ty<'_>) -> Option<DefId> {
    let mir_ty::TyKind::Dynamic(preds, ..) = ty.kind() else {
        unreachable!("not a trait object: {ty:?}");
    };
    preds.principal_def_id()
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
        let source = self.operand_type(operand);
        if hidden_ty.is_trait() {
            self.check_auto_trait_drop(hidden_ty, dyn_ty);
        } else {
            self.check_vtable_methods(hidden_ty, dyn_ty);
            self.require_hidden_invariant(source_ty, hidden_ty, source.clone());
        }
        let expected_ty = self.type_builder.build(ty).vacuous().ty;
        let mut builder = PlaceTypeBuilder::default();
        let _ = builder.subsume(source);
        let term = if expected_ty.is_mut() {
            chc::Term::mut_(chc::Term::null(), chc::Term::null())
        } else {
            chc::Term::box_(chc::Term::null())
        };
        builder.build(expected_ty, term)
    }

    /// Stops at a coercion between trait objects unless it only drops auto traits
    /// (`dyn Tr + Sync` to `dyn Tr`), which keeps the vtable.
    fn check_auto_trait_drop(&self, source_dyn: mir_ty::Ty<'tcx>, dyn_ty: mir_ty::Ty<'tcx>) {
        if principal_def_id(source_dyn) == principal_def_id(dyn_ty) {
            return;
        }
        self.tcx.dcx().fatal(format!(
            "a trait object coerced to one of another trait (`{source_dyn}` to `{dyn_ty}` in \
             `{}`) is not supported",
            self.tcx.def_path_str(self.type_builder.owner_fn_id()),
        ));
    }

    /// Requires the type invariant of the value packed into a trait object, as a parameter of
    /// type `&T`, `&mut T` or `Box<T>` requires it: the impl's methods are checked assuming it,
    /// and a call through the trait object does not state it.
    fn require_hidden_invariant(
        &mut self,
        source_ty: mir_ty::Ty<'tcx>,
        hidden_ty: mir_ty::Ty<'tcx>,
        source: PlaceType,
    ) {
        let owner = self.type_builder.owner_fn_id();
        let Some(pred) = self
            .ctx
            .type_invariant_pred(&self.type_builder, owner, hidden_ty)
        else {
            return;
        };
        let value = chc::Term::var(rty::RefinedTypeVar::Value);
        let current = if source_ty.is_mutable_ptr() {
            value.mut_current()
        } else {
            value.box_current()
        };
        let invariant = chc::Formula::Atom(chc::Atom::new(pred, vec![current]));
        let expected = rty::RefinedType::<Var>::new(source.ty.clone(), invariant.into());
        let got: rty::RefinedType<Var> = source.into();
        let clauses = self.env.relate_sub_refined_type(&got, &expected);
        self.ctx.extend_clauses(clauses);
    }

    /// Requests the type of each method of `hidden_ty`'s impl of `dyn_ty`'s trait and its
    /// supertraits that a call through the vtable may reach with a contract, so that its body is
    /// checked against the trait's contract.
    fn check_vtable_methods(&mut self, hidden_ty: mir_ty::Ty<'tcx>, dyn_ty: mir_ty::Ty<'tcx>) {
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
            if !seen.insert(trait_ref) {
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
                    || self.ctx.written_contract_formulas(method.def_id).is_empty()
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
                self.check_invariant_kept(hidden_ty, dyn_ty, method.def_id, args);
                let _ = self.callable_ty(method.def_id, args);
            }
            pending.extend(analyze::extern_spec::supertrait_bounds(self.tcx, trait_ref));
        }
    }

    /// Stops unless the vtable method `def_id` at `args`, if it takes `&mut self` of a type with
    /// an invariant, ensures the invariant of the receiver's final value, as its contract does
    /// unless the receiver is `#[thrust::open_inv]` or its borrow may outlive the call (a returned
    /// `&mut` into it). Calls through the trait object assume the invariant of the packed value,
    /// which only the impl's methods change.
    fn check_invariant_kept(
        &self,
        hidden_ty: mir_ty::Ty<'tcx>,
        dyn_ty: mir_ty::Ty<'tcx>,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) {
        let tcx = self.tcx;
        let receiver = tcx.fn_sig(def_id).skip_binder().inputs().skip_binder()[0];
        if !receiver.is_mutable_ptr() {
            return;
        }
        let owner = self.type_builder.owner_fn_id();
        if self
            .ctx
            .type_invariant_pred(&self.type_builder, owner, hidden_ty)
            .is_none()
        {
            return;
        }
        let resolved = mir_ty::Instance::try_resolve(tcx, self.typing_env, def_id, args)
            .ok()
            .flatten()
            .map_or(def_id, |instance| instance.def_id());
        let open_inv = [def_id, resolved].into_iter().any(|def_id| {
            def_id
                .as_local()
                .and_then(|local| tcx.hir_maybe_body_owned_by(local))
                .and_then(|body| body.params.first())
                .is_some_and(|param| {
                    tcx.hir_attrs(param.hir_id)
                        .iter()
                        .any(|attr| attr.path_matches(&analyze::annot::open_inv_path()))
                })
        });
        if !open_inv && !analyze::local_def::borrow_may_escape(tcx, resolved, 0) {
            return;
        }
        tcx.dcx().fatal(format!(
            "`{hidden_ty}` packed into `{dyn_ty}` in `{}` is not supported: its invariant is not \
             ensured after `{}`, whose `&mut self` is `#[thrust::open_inv]` or may outlive the \
             call, and calls through the trait object assume it",
            tcx.def_path_str(owner),
            tcx.def_path_str(resolved),
        ));
    }

    /// Stops unless the trait `trait_def_id`, reached through the trait object `dyn_ty`, is a
    /// trait of the crate that declares no law, logic function or predicate: those would be
    /// assumed of `dyn_ty`, which no impl proves them of (Creusot's `unsound_dyn`).
    fn check_dyn_trait(&self, trait_def_id: DefId, dyn_ty: mir_ty::Ty<'tcx>) {
        let tcx = self.tcx;
        let owner = tcx.def_path_str(self.type_builder.owner_fn_id());
        let trait_name = tcx.def_path_str(trait_def_id);
        if !trait_def_id.is_local() {
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

    /// Whether the call of `def_id` at `args` goes through a vtable.
    pub(super) fn is_virtual_call(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> bool {
        if self.tcx.trait_of_assoc(def_id).is_none() || !args.type_at(0).is_trait() {
            return false;
        }
        let instance = mir_ty::Instance::try_resolve(self.tcx, self.typing_env, def_id, args);
        matches!(
            instance,
            Ok(Some(mir_ty::Instance {
                def: mir_ty::InstanceKind::Virtual(..),
                ..
            }))
        )
    }

    /// Stops at a call of the trait method `def_id` through the trait object `args[0]` unless
    /// the trait gives the method a written contract that does not mention `self` or `Self`.
    pub(super) fn check_dyn_call(&self, def_id: DefId, args: mir_ty::GenericArgsRef<'tcx>) {
        let tcx = self.tcx;
        let dyn_ty = args.type_at(0);
        let trait_def_id = tcx.trait_of_assoc(def_id).expect("a trait method");
        self.check_dyn_trait(trait_def_id, dyn_ty);
        let owner = tcx.def_path_str(self.type_builder.owner_fn_id());
        let method = tcx.def_path_str(def_id);
        let formulas = self.ctx.written_contract_formulas(def_id);
        if formulas.is_empty() {
            tcx.dcx().fatal(format!(
                "`{method}` is called through `{dyn_ty}` in `{owner}`, but has no contract on the \
                 trait: a call through a trait object takes the trait's contract"
            ));
        }
        if self.ctx.contract_names_self(&formulas) {
            tcx.dcx().fatal(format!(
                "`{method}` is called through `{dyn_ty}` in `{owner}`, but its contract mentions \
                 `self` or `Self`, whose model a trait object does not have"
            ));
        }
    }

    /// Stops at a call that instantiates a type parameter with a trait object (`g::<dyn Tr>`, or
    /// an impl for `Box<T>` at `T = dyn Tr`): the callee's contract and the laws of its bounds
    /// would be assumed of `dyn Tr`. The type arguments from `from` on are checked.
    pub(super) fn check_no_dyn_type_arg(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        from: usize,
    ) {
        let Some(dyn_ty) = args.types().skip(from).find(|ty| ty.is_trait()) else {
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
