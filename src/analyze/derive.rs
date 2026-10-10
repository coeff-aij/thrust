//! The impls rustc's built-in derives generate.
//!
//! The Rust Reference fixes what each built-in derive generates, so a method of such an impl
//! is not analyzed when that semantics implies the contract std.rs gives the trait method:
//!
//! - `PartialEq::eq` compares the fields with `==`, and `Clone::clone` clones each field, so
//!   they are `result == (*x == *y)` and `result == *x` when the type's model is the tuple (or
//!   datatype) of its fields' models and `==` and `clone` of every field act on its model.
//! - `Hash::hash` and `Default::default` call the same method of each field, whose contracts
//!   (no panic, nothing more) they then have.
//! - `PartialOrd::partial_cmp` and `Ord::cmp` compare the fields lexicographically in declaration
//!   order, and a fieldless enum by its discriminants. A type with such a derive and no
//!   `PartialOrdSpec` impl is given that order as its `compares` relation ([`Compares`]), from
//!   the relations of its fields, and the two methods have std.rs's contracts over it.
//! - `Debug::fmt` writes to a `Formatter`, which has no model; it is left out, as
//!   `#[thrust::ignored]`.

use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeVisitableExt as _};
use rustc_span::def_id::DefId;
use rustc_span::sym;

use crate::analyze::{self, DefIdCache};
use crate::chc;
use crate::refine::{self, TypeBuilder};

/// How a method of an impl a built-in derive generated is treated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Treatment {
    /// The body is not analyzed; the method has the contract of the trait method.
    Trusted,
    /// The method is not verified, and a call to it is not supported.
    Ignored,
}

/// The treatment of `def_id` when it is a method of an impl one of rustc's built-in derives
/// generated, and `None` when its body is analyzed as any other.
pub fn treatment<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    def_id: DefId,
) -> Option<Treatment> {
    let impl_did = tcx.impl_of_assoc(def_id)?;
    if !tcx.is_builtin_derived(impl_did) {
        return None;
    }
    let trait_did = tcx.trait_id_of_impl(impl_did)?;
    let self_ty = tcx.type_of(impl_did).instantiate_identity();
    let typing_env = mir_ty::TypingEnv::post_analysis(tcx, impl_did);
    let trusted = match tcx.get_diagnostic_name(trait_did)? {
        sym::Debug => return Some(Treatment::Ignored),
        sym::Hash | sym::Default => true,
        sym::PartialEq | sym::Clone => {
            has_structural_model(tcx, def_ids, typing_env, self_ty)
                && field_tys(tcx, self_ty)
                    .into_iter()
                    .all(|ty| acts_on_model(tcx, def_ids, ty))
        }
        sym::PartialOrd | sym::Ord => has_generated_compares(tcx, def_ids, self_ty),
        _ => false,
    };
    trusted.then_some(Treatment::Trusted)
}

/// Whether `clause` is `ty: PartialOrdSpec` for a `ty` whose `compares` is generated.
pub fn holds_by_generated_compares<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    clause: mir_ty::Clause<'tcx>,
) -> bool {
    clause.as_trait_clause().is_some_and(|pred| {
        let trait_ref = pred.skip_binder().trait_ref;
        Some(trait_ref.def_id) == def_ids.partial_ord_spec()
            && has_generated_compares(tcx, def_ids, trait_ref.self_ty())
    })
}

/// Whether `ty` takes its `PartialOrdSpec::compares` from its derived `PartialOrd`: `ty` is a
/// struct whose fields each have a `compares` (or are `PhantomData`), or a fieldless enum; its
/// `PartialOrd` impl is the built-in derive; its model is structural; and it has no
/// `PartialOrdSpec` impl of its own.
pub fn has_generated_compares<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    let Some(spec_trait) = def_ids.partial_ord_spec() else {
        return false;
    };
    let mir_ty::TyKind::Adt(adt, _) = ty.kind() else {
        return false;
    };
    let typing_env = mir_ty::TypingEnv::fully_monomorphized();
    if ty.has_param()
        || implements(tcx, spec_trait, ty)
        || !has_derived_partial_ord(tcx, adt.did())
        || !has_structural_model(tcx, def_ids, typing_env, ty)
    {
        return false;
    }
    if adt.is_enum() {
        return !adt.variants().is_empty() && adt.all_fields().next().is_none();
    }
    field_tys(tcx, ty).into_iter().all(|field_ty| {
        is_phantom_data(tcx, field_ty)
            || implements(tcx, spec_trait, field_ty)
            || has_generated_compares(tcx, def_ids, field_ty)
    })
}

fn has_derived_partial_ord(tcx: TyCtxt<'_>, adt_did: DefId) -> bool {
    let Some(partial_ord) = tcx.lang_items().partial_ord_trait() else {
        return false;
    };
    tcx.all_local_trait_impls(())
        .get(&partial_ord)
        .into_iter()
        .flatten()
        .any(|impl_did| {
            let self_ty = tcx.type_of(*impl_did).instantiate_identity();
            self_ty.ty_adt_def().map(|adt| adt.did()) == Some(adt_did)
                && tcx.is_builtin_derived(impl_did.to_def_id())
        })
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

/// Whether the model of `ty` is `ty` itself: the tuple of its fields' models for a struct, the
/// datatype of them for an enum. A type without a `Model` impl has that model.
fn has_structural_model<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    let Some(model_ty) = def_ids.model_ty() else {
        return true;
    };
    let ty = tcx.erase_regions(ty);
    let projection = mir_ty::Ty::new_projection(tcx, model_ty, [ty]);
    match tcx.try_normalize_erasing_regions(typing_env, projection) {
        Ok(model) => model == ty || model == projection,
        Err(_) => true,
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

/// Whether `==` and `clone` on a value of `ty` are equality and identity of its model, as
/// std.rs's `PartialEq::eq` and `Clone::clone` specs state. They are not for a `&mut` (its model
/// has the final value), a float (NaN), a raw or function pointer (compared by address), or a
/// `Ghost` (whose `PartialEq` is for formulas only); `PhantomData` compares equal at any argument.
fn acts_on_model<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &DefIdCache<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        mir_ty::TyKind::Bool
        | mir_ty::TyKind::Char
        | mir_ty::TyKind::Int(_)
        | mir_ty::TyKind::Uint(_)
        | mir_ty::TyKind::Str
        | mir_ty::TyKind::Never
        | mir_ty::TyKind::Param(_) => true,
        mir_ty::TyKind::Ref(_, ty, mir_ty::Mutability::Not)
        | mir_ty::TyKind::Array(ty, _)
        | mir_ty::TyKind::Slice(ty) => acts_on_model(tcx, def_ids, *ty),
        mir_ty::TyKind::Tuple(tys) => tys.iter().all(|ty| acts_on_model(tcx, def_ids, ty)),
        mir_ty::TyKind::Adt(adt, args) => {
            is_phantom_data(tcx, ty)
                || (Some(adt.did()) != def_ids.ghost_model()
                    && args.types().all(|ty| acts_on_model(tcx, def_ids, ty)))
        }
        _ => false,
    }
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
        if has_generated_compares(self.tcx, &self.analyzer.def_ids(), ty) {
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
        let v_sym = chc::DatatypeSymbol::new(format!("{}.{}", d_sym, variant));
        chc::Term::datatype_ctor(d_sym, sort_args, v_sym, fields)
    }
}
