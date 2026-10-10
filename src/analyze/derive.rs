//! The impls rustc's built-in derives generate.
//!
//! The Rust Reference fixes what each built-in derive generates, so a method of such an impl
//! is not analyzed when that semantics implies the contract std.rs gives the trait method:
//!
//! - `PartialEq::eq` compares the fields with `==`, and `Clone::clone` clones each field, so
//!   they are `result == (*x == *y)` and `result == *x` when the type's model is the tuple (or
//!   datatype) of its fields' models, or the model of its one field besides `PhantomData`s. For
//!   `eq`, `==` on the type must also be equality of models, as std.rs's `ModelEq` decides it,
//!   and no field may hold a `Ghost`, whose `PartialEq` is for formulas only: analyzing the body
//!   rejects that call. A clone acts on the model of every type, as std.rs's spec states.
//! - `Hash::hash` and `Default::default` call the same method of each field, whose contracts
//!   (no panic, nothing more) they then have.
//! - `PartialOrd::partial_cmp` and `Ord::cmp` compare the fields lexicographically in declaration
//!   order, and a fieldless enum by its discriminants. A type with such a derive and no
//!   `PartialOrdSpec` impl is given that order as its `compares` relation ([`Compares`]), from
//!   the relations of its fields, and the two methods have std.rs's contracts over it.

use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeVisitableExt as _};
use rustc_span::def_id::DefId;
use rustc_span::sym;

use crate::analyze::{self, DefIdCache};
use crate::chc;
use crate::refine::{self, TypeBuilder};

/// Whether `def_id` is a method of an impl one of rustc's built-in derives generated whose body
/// is not analyzed: it has the contract of the trait method.
pub fn is_trusted<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    type_builder: &TypeBuilder<'tcx>,
    def_id: DefId,
) -> bool {
    let Some(impl_did) = tcx.impl_of_assoc(def_id) else {
        return false;
    };
    if !tcx.is_builtin_derived(impl_did) {
        return false;
    }
    let Some(trait_did) = tcx.trait_id_of_impl(impl_did) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_did).instantiate_identity();
    let has_fields_model = || {
        has_structural_model(type_builder, self_ty)
            || has_transparent_model(tcx, def_ids, type_builder, self_ty)
    };
    match tcx.get_diagnostic_name(trait_did) {
        Some(sym::Hash | sym::Default) => true,
        Some(sym::PartialEq) => {
            has_fields_model()
                && !matches!(analyze::model_eq(tcx, self_ty), analyze::SpecBound::Fails)
                && !holds_ghost(tcx, def_ids, self_ty)
        }
        Some(sym::Clone) => has_fields_model(),
        Some(sym::PartialOrd | sym::Ord) => {
            has_generated_compares(tcx, def_ids, type_builder, self_ty)
        }
        _ => false,
    }
}

/// Whether a field of the ADT `ty` holds a `Ghost`.
fn holds_ghost<'tcx>(tcx: TyCtxt<'tcx>, def_ids: &DefIdCache<'tcx>, ty: mir_ty::Ty<'tcx>) -> bool {
    let Some(ghost) = def_ids.ghost_model() else {
        return false;
    };
    field_tys(tcx, ty).into_iter().any(|field_ty| {
        field_ty
            .walk()
            .filter_map(|arg| arg.as_type())
            .any(|ty| ty.ty_adt_def().is_some_and(|adt| adt.did() == ghost))
    })
}

/// Whether `clause` is `ty: PartialOrdSpec` for a `ty` whose `compares` is generated.
pub fn holds_by_generated_compares<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    type_builder: &TypeBuilder<'tcx>,
    clause: mir_ty::Clause<'tcx>,
) -> bool {
    clause.as_trait_clause().is_some_and(|pred| {
        let trait_ref = pred.skip_binder().trait_ref;
        Some(trait_ref.def_id) == def_ids.partial_ord_spec()
            && has_generated_compares(tcx, def_ids, type_builder, trait_ref.self_ty())
    })
}

/// Whether `ty` takes its `PartialOrdSpec::compares` from its derived `PartialOrd`: `ty` is a
/// struct whose fields each have a `compares` (or are `PhantomData`), or a fieldless enum; its
/// `PartialOrd` impl is the built-in derive; its model is structural; and it has no
/// `PartialOrdSpec` impl of its own.
pub fn has_generated_compares<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    type_builder: &TypeBuilder<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    let Some(spec_trait) = def_ids.partial_ord_spec() else {
        return false;
    };
    let mir_ty::TyKind::Adt(adt, _) = ty.kind() else {
        return false;
    };
    if ty.has_param()
        || implements(tcx, spec_trait, ty)
        || !has_derived_partial_ord(tcx, ty)
        || !has_structural_model(type_builder, ty)
    {
        return false;
    }
    if adt.is_enum() {
        return !adt.variants().is_empty() && adt.all_fields().next().is_none();
    }
    field_tys(tcx, ty).into_iter().all(|field_ty| {
        is_phantom_data(tcx, field_ty)
            || implements(tcx, spec_trait, field_ty)
            || has_generated_compares(tcx, def_ids, type_builder, field_ty)
    })
}

/// Whether the `PartialOrd` impl of `ty` is the built-in derive.
fn has_derived_partial_ord<'tcx>(tcx: TyCtxt<'tcx>, ty: mir_ty::Ty<'tcx>) -> bool {
    let Some(partial_cmp) = tcx.get_diagnostic_item(sym::cmp_partialord_cmp) else {
        return false;
    };
    let args = tcx.mk_args(&[ty.into(), ty.into()]);
    let typing_env = mir_ty::TypingEnv::fully_monomorphized();
    let Ok(Some(instance)) = mir_ty::Instance::try_resolve(tcx, typing_env, partial_cmp, args)
    else {
        return false;
    };
    tcx.impl_of_assoc(instance.def_id())
        .is_some_and(|impl_did| tcx.is_builtin_derived(impl_did))
}

fn implements<'tcx>(tcx: TyCtxt<'tcx>, trait_did: DefId, ty: mir_ty::Ty<'tcx>) -> bool {
    use rustc_infer::infer::TyCtxtInferExt as _;
    use rustc_trait_selection::infer::InferCtxtExt as _;

    let (infcx, param_env) = tcx
        .infer_ctxt()
        .build_with_typing_env(mir_ty::TypingEnv::fully_monomorphized());
    infcx
        .type_implements_trait(trait_did, [ty], param_env)
        .must_apply_modulo_regions()
}

/// Whether the model of the ADT `ty` is the same ADT (at its arguments' models): the tuple of its
/// fields' models for a struct, the datatype of them for an enum. A type without a `Model` impl
/// has that model.
fn has_structural_model<'tcx>(type_builder: &TypeBuilder<'tcx>, ty: mir_ty::Ty<'tcx>) -> bool {
    let model = type_builder.resolve_model_ty(ty);
    model.ty_adt_def().is_some() && model.ty_adt_def() == ty.ty_adt_def()
}

/// Whether the model of the struct `ty` is the model of one of its fields, the others being
/// `PhantomData`.
fn has_transparent_model<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    type_builder: &TypeBuilder<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    if !ty.ty_adt_def().is_some_and(|adt| adt.is_struct()) {
        return false;
    }
    let live: Vec<_> = field_tys(tcx, ty)
        .into_iter()
        .filter(|field_ty| !is_phantom_data(tcx, *field_ty))
        .collect();
    let [field_ty] = live[..] else {
        return false;
    };
    model_of(def_ids, type_builder, field_ty) == model_of(def_ids, type_builder, ty)
}

/// The model of `ty`, with a `<X as Model>::Ty` left unresolved taken as the model of `X`, as
/// [`TypeBuilder::build`] takes it (the model of a type parameter is the parameter).
fn model_of<'tcx>(
    def_ids: &DefIdCache<'tcx>,
    type_builder: &TypeBuilder<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> mir_ty::Ty<'tcx> {
    let model = type_builder.resolve_model_ty(ty);
    match model.kind() {
        mir_ty::TyKind::Alias(mir_ty::AliasTyKind::Projection, alias)
            if Some(alias.def_id) == def_ids.model_ty() =>
        {
            type_builder.resolve_model_ty(alias.self_ty())
        }
        _ => model,
    }
}

/// The types of the fields of every variant of the ADT `ty`.
fn field_tys<'tcx>(tcx: TyCtxt<'tcx>, ty: mir_ty::Ty<'tcx>) -> Vec<mir_ty::Ty<'tcx>> {
    let mir_ty::TyKind::Adt(adt, args) = ty.kind() else {
        return Vec::new();
    };
    adt.all_fields().map(|field| field.ty(tcx, args)).collect()
}

fn is_phantom_data(tcx: TyCtxt<'_>, ty: mir_ty::Ty<'_>) -> bool {
    ty.ty_adt_def().map(|adt| adt.did()) == tcx.lang_items().phantom_data()
}

/// The generated `compares` relation of a type for which [`has_generated_compares`] holds,
/// as a formula. A field's relation is its type's `compares` predicate, or its own generated
/// relation; a `PhantomData` field compares equal.
pub struct Compares<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    analyzer: &'a analyze::Analyzer<'tcx>,
    type_builder: &'a TypeBuilder<'tcx>,
    /// `PartialOrdSpec::compares`
    compares: DefId,
}

impl<'a, 'tcx> Compares<'a, 'tcx> {
    pub fn new(
        analyzer: &'a analyze::Analyzer<'tcx>,
        type_builder: &'a TypeBuilder<'tcx>,
        compares: DefId,
    ) -> Self {
        Self {
            tcx: analyzer.tcx(),
            analyzer,
            type_builder,
            compares,
        }
    }

    /// `ty::compares(x, y, ord)`: for a struct, the first field whose relation does not hold at
    /// `Some(Equal)` decides `ord`, as the derived `partial_cmp` returns the first field's result
    /// that is not `Some(Equal)`; for a fieldless enum, the order of the discriminants.
    pub fn formula<V>(
        &self,
        ty: mir_ty::Ty<'tcx>,
        x: chc::Term<V>,
        y: chc::Term<V>,
        ord: chc::Term<V>,
    ) -> chc::Formula<V>
    where
        V: Clone,
    {
        let adt = ty.ty_adt_def().expect("a generated compares is of an ADT");
        if adt.is_enum() {
            let d_sym = refine::datatype_symbol(self.tcx, adt.did());
            return self.int_compares(
                chc::Term::datatype_discr(d_sym.clone(), x),
                chc::Term::datatype_discr(d_sym, y),
                ord,
            );
        }
        let fields = field_tys(self.tcx, ty);
        let Some((last, init)) = fields.split_last() else {
            return chc::Formula::Atom(ord.equal_to(self.ordering("Equal")));
        };
        let field = |idx: usize, ty, ord| {
            self.field_formula(
                ty,
                x.clone().tuple_proj(idx),
                y.clone().tuple_proj(idx),
                ord,
            )
        };
        let mut formula = field(init.len(), *last, ord.clone());
        for (idx, ty) in init.iter().enumerate().rev() {
            let equal = field(idx, *ty, self.ordering("Equal"));
            let decided = field(idx, *ty, ord.clone());
            formula = equal.clone().and(formula).or(equal.not().and(decided));
        }
        formula
    }

    fn field_formula<V>(
        &self,
        ty: mir_ty::Ty<'tcx>,
        x: chc::Term<V>,
        y: chc::Term<V>,
        ord: chc::Term<V>,
    ) -> chc::Formula<V>
    where
        V: Clone,
    {
        if is_phantom_data(self.tcx, ty) {
            return chc::Formula::Atom(ord.equal_to(self.ordering("Equal")));
        }
        if has_generated_compares(self.tcx, &self.analyzer.def_ids(), self.type_builder, ty) {
            return self.formula(ty, x, y, ord);
        }
        let instance = mir_ty::Instance::try_resolve(
            self.tcx,
            mir_ty::TypingEnv::fully_monomorphized(),
            self.compares,
            self.tcx.mk_args(&[ty.into()]),
        )
        .unwrap()
        .expect("a field of a type with a generated compares implements PartialOrdSpec");
        let pred = self.analyzer.predicate_with_args(
            instance.def_id(),
            instance.args,
            self.type_builder.owner_fn_id(),
        );
        chc::Formula::Atom(chc::Atom::new(pred.into(), vec![x, y, ord]))
    }

    /// The `compares` of the integers in std.rs.
    fn int_compares<V>(
        &self,
        x: chc::Term<V>,
        y: chc::Term<V>,
        ord: chc::Term<V>,
    ) -> chc::Formula<V>
    where
        V: Clone,
    {
        let case = |pred: chc::KnownPred, variant| {
            chc::Formula::Atom(chc::Atom::new(pred.into(), vec![x.clone(), y.clone()])).and(
                chc::Formula::Atom(ord.clone().equal_to(self.ordering(variant))),
            )
        };
        case(chc::KnownPred::LESS_THAN, "Less")
            .or(case(chc::KnownPred::EQUAL, "Equal"))
            .or(case(chc::KnownPred::GREATER_THAN, "Greater"))
    }

    /// `Some(Ordering::<variant>)`.
    fn ordering<V>(&self, variant: &str) -> chc::Term<V> {
        let lang_items = self.tcx.lang_items();
        let ordering_did = lang_items.ordering_enum().unwrap();
        let option_did = lang_items.option_type().unwrap();
        let ordering_ty = self.tcx.type_of(ordering_did).instantiate_identity();
        let ordering = self.ctor(ordering_did, variant, Vec::new(), Vec::new());
        let ordering_sort = self.type_builder.build(ordering_ty).to_sort();
        self.ctor(option_did, "Some", vec![ordering_sort], vec![ordering])
    }

    fn ctor<V>(
        &self,
        adt_did: DefId,
        variant: &str,
        sort_args: Vec<chc::Sort>,
        fields: Vec<chc::Term<V>>,
    ) -> chc::Term<V> {
        let d_sym = refine::datatype_symbol(self.tcx, adt_did);
        let v_sym = refine::variant_symbol(&d_sym, variant);
        chc::Term::datatype_ctor(d_sym, sort_args, v_sym, fields)
    }
}
