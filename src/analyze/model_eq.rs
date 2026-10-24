//! Whether `==` on a type is equality of its models, decided from the type's structure: for the
//! `ModelEq` bounds of extern specs and the derived `PartialEq` of a type with a model.

use std::collections::HashSet;

use rustc_hir::lang_items::LangItem;
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;

use crate::analyze;

/// How a spec's bound stands at the arguments it was bound to, in a caller's environment.
pub(super) enum SpecBound {
    Holds,
    /// The bound's self type is a type parameter or an unresolved projection of the caller.
    Assumed,
    Fails,
}

pub(super) fn is_model_eq_clause(tcx: TyCtxt<'_>, clause: mir_ty::Clause<'_>) -> bool {
    clause.as_trait_clause().is_some_and(|pred| {
        tcx.get_attrs_by_path(
            pred.skip_binder().trait_ref.def_id,
            &analyze::annot::model_eq_path(),
        )
        .next()
        .is_some()
    })
}

/// `ty: ModelEq` of std.rs, decided by [`model_eq`].
pub(super) fn model_eq_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    model_trait: DefId,
    clause: mir_ty::Clause<'tcx>,
) -> SpecBound {
    let self_ty = clause.as_trait_clause().unwrap().skip_binder().self_ty();
    let self_ty = tcx
        .try_normalize_erasing_regions(typing_env, self_ty)
        .unwrap_or(self_ty);
    model_eq(tcx, model_trait, self_ty)
}

/// Whether `==` on values of `ty` is equality of their models, decided from the structure of
/// `ty`. It is not when `ty` holds a `&mut` (its model also has the final value, which `==` does
/// not read), a float (NaN), a raw or function pointer (compared by address), a trait object or
/// a `str` (opaque, of the null sort, so all values of one have one model), or a `Ghost` (which
/// has no `PartialEq`, so a hand-written `eq` of a type holding one leaves it out). A type
/// parameter or an unresolved projection in `ty` makes it assumed. `model_trait` is
/// `thrust_models::Model`.
pub(super) fn model_eq<'tcx>(
    tcx: TyCtxt<'tcx>,
    model_trait: DefId,
    ty: mir_ty::Ty<'tcx>,
) -> SpecBound {
    let mut assumed = false;
    for ty in compared_tys(tcx, Some(model_trait), ty) {
        match ty.kind() {
            mir_ty::TyKind::Ref(_, _, mir_ty::Mutability::Mut)
            | mir_ty::TyKind::Float(_)
            | mir_ty::TyKind::RawPtr(..)
            | mir_ty::TyKind::FnPtr(..)
            | mir_ty::TyKind::Dynamic(..)
            | mir_ty::TyKind::Str => return SpecBound::Fails,
            mir_ty::TyKind::Adt(adt, _) if is_ghost(tcx, adt.did()) => return SpecBound::Fails,
            mir_ty::TyKind::Param(_) | mir_ty::TyKind::Alias(..) => assumed = true,
            _ => {}
        }
    }
    if assumed {
        SpecBound::Assumed
    } else {
        SpecBound::Holds
    }
}

/// Whether `==` on values of `ty` compares a `Ghost`, as [`model_eq`] looks into `ty`.
pub(super) fn compares_ghost<'tcx>(tcx: TyCtxt<'tcx>, ty: mir_ty::Ty<'tcx>) -> bool {
    compared_tys(tcx, None, ty)
        .into_iter()
        .any(|ty| ty.ty_adt_def().is_some_and(|adt| is_ghost(tcx, adt.did())))
}

/// The types in `ty` whose `==` the `==` on `ty` may run, or whose models the model of `ty` is
/// built from: a local ADT is looked into through its fields, a foreign one through its type
/// arguments, and also through its fields when `model_trait` is given and the ADT has no `Model`
/// impl, since its model is then the tuple of its fields' (a raw pointer inside `Rc` or `NonNull`
/// gives all their values one model); a `PhantomData` compares equal at any argument.
fn compared_tys<'tcx>(
    tcx: TyCtxt<'tcx>,
    model_trait: Option<DefId>,
    ty: mir_ty::Ty<'tcx>,
) -> Vec<mir_ty::Ty<'tcx>> {
    let mut compared = Vec::new();
    let mut visited = HashSet::new();
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        if !visited.insert(ty) {
            continue;
        }
        let mut walker = ty.walk();
        while let Some(arg) = walker.next() {
            let Some(ty) = arg.as_type() else {
                continue;
            };
            match ty.kind() {
                mir_ty::TyKind::Adt(adt, _)
                    if tcx.is_lang_item(adt.did(), LangItem::PhantomData) =>
                {
                    walker.skip_current_subtree();
                    continue;
                }
                mir_ty::TyKind::Adt(adt, args)
                    if adt.did().is_local() && !is_ghost(tcx, adt.did()) =>
                {
                    pending.extend(adt.all_fields().map(|field| field.ty(tcx, args)));
                }
                mir_ty::TyKind::Adt(adt, args)
                    if model_trait.is_some_and(|t| !has_model_impl(tcx, t, adt.did())) =>
                {
                    pending.extend(adt.all_fields().map(|field| field.ty(tcx, args)));
                }
                _ => {}
            }
            compared.push(ty);
        }
    }
    compared
}

/// Whether an impl of `model_trait` (`thrust_models::Model`) is for the ADT `adt`, at any type
/// arguments: an impl for one instance counts for all, which is exact for std.rs, whose `Model`
/// impls of std types are generic over their arguments.
fn has_model_impl(tcx: TyCtxt<'_>, model_trait: DefId, adt: DefId) -> bool {
    tcx.all_impls(model_trait).any(|impl_did| {
        tcx.type_of(impl_did)
            .instantiate_identity()
            .ty_adt_def()
            .is_some_and(|impl_adt| impl_adt.did() == adt)
    })
}

fn is_ghost(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.get_attrs_by_path(def_id, &analyze::annot::ghost_model_path())
        .next()
        .is_some()
}
