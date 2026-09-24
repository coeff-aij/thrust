use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Mutability};
use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

use super::basic_block::BasicBlockType;
use crate::analyze::{DefIdCache, TypeParam, TypeParamMap};
use crate::chc;
use crate::refine;
use crate::rty;

/// The model of a contiguous sequence of `elem_ty`: the `(elements, length)` pair that
/// `thrust_models` gives to `Vec<T>`, `[T]` and `[T; N]` alike.
///
/// A concrete element type never needs this: `<Vec<i64> as Model>::Ty` normalizes all the way
/// to `model::Seq<model::Int>`, whose fields are traversed as a struct into the very same pair.
///
/// A generic element type does not get that far, in either of two ways. Where the element type
/// is bounded by `Model`, the projection normalizes to `Seq<<T as Model>::Ty>` but the nested
/// alias it leaves behind makes `resolve_model_ty` discard the normalization and hand back the
/// original type. Where it is not, the projection does not normalize at all, since `T: Model`
/// is not provable. Neither leaves an ADT to traverse, so the pair is spelled out here instead.
fn seq_model_type<V>(elem_ty: rty::Type<V>) -> rty::Type<V> {
    let array_ty = rty::ArrayType::new(rty::Type::int(), elem_ty);
    rty::TupleType::new(vec![
        rty::PointerType::own(rty::Type::Array(array_ty)).into(),
        rty::PointerType::own(rty::Type::int()).into(),
    ])
    .into()
}

/// The model of an iterator over a contiguous sequence: the `(base, cursor)` pair, where the
/// cursor is the position of the element the next `next` will return and the base is the whole
/// sequence the iterator was made from.
///
/// Spelling the pair out here is what lets the element type be a type parameter, the same way
/// `seq_model_type` does for the sequence types themselves. Unlike those, though, the struct
/// traversal is not merely unhelpful for these three but impossible: every one of them reaches
/// a `*const T` through `NonNull`, which has no model at any element type at all.
fn seq_iter_model_type<V>(base_ty: rty::Type<V>) -> rty::Type<V> {
    rty::TupleType::new(vec![
        rty::PointerType::own(base_ty).into(),
        rty::PointerType::own(rty::Type::int()).into(),
    ])
    .into()
}

/// The model of `slice::IterMut`: the two halves of the `&mut [T]` it was made from, as
/// separate sequences, and the cursor.
///
/// The two halves are named rather than carried as one `Mut`, because a `Mut` here would not
/// be a borrow of the iterator's own. The drop rule resolves every `Mut` it finds while
/// walking a dying local's model, which is right for a borrow that ends there and wrong for a
/// second name of a pair the caller still holds: the iterator freezes its base, so the pair's
/// current half stops following the writes, and resolving it would equate what the caller
/// passed in with what the writes produced. `iter_mut` relates the two sequences to the
/// reference itself, and states the length preservation that the drop rule used to supply.
fn mut_seq_iter_model_type<V: Clone>(seq_ty: rty::Type<V>) -> rty::Type<V> {
    rty::TupleType::new(vec![
        rty::PointerType::own(seq_ty.clone()).into(),
        rty::PointerType::own(seq_ty).into(),
        rty::PointerType::own(rty::Type::int()).into(),
    ])
    .into()
}

/// The element type of one of the three sequence iterators.
///
/// It is the first type argument, but not the first argument: `slice::Iter` and
/// `slice::IterMut` take a lifetime ahead of it and `vec::IntoIter` an allocator behind it.
fn iterated_elem_ty<'tcx>(
    ty: mir_ty::Ty<'tcx>,
    args: &'tcx mir_ty::List<mir_ty::GenericArg<'tcx>>,
) -> mir_ty::Ty<'tcx> {
    args.types()
        .next()
        .unwrap_or_else(|| panic!("sequence iterator without an element type: {ty:?}"))
}

pub trait TemplateRegistry {
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V>;
}

impl<T> TemplateRegistry for &mut T
where
    T: TemplateRegistry + ?Sized,
{
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V> {
        T::register_template(self, tmpl)
    }
}

/// [`TemplateScope`] with no variables in scope.
#[derive(Clone, Default)]
pub struct EmptyTemplateScope;

impl TemplateScope for EmptyTemplateScope {
    type Var = rty::Closed;
    fn build_template(&self) -> rty::TemplateBuilder<Self::Var> {
        rty::TemplateBuilder::default()
    }
}

pub trait TemplateScope {
    type Var: chc::Var;
    fn build_template(&self) -> rty::TemplateBuilder<Self::Var>;
}

impl<T> TemplateScope for &T
where
    T: TemplateScope,
{
    type Var = T::Var;
    fn build_template(&self) -> rty::TemplateBuilder<Self::Var> {
        T::build_template(self)
    }
}

impl<T> TemplateScope for rty::TemplateBuilder<T>
where
    T: chc::Var,
{
    type Var = T;
    fn build_template(&self) -> rty::TemplateBuilder<T> {
        self.clone()
    }
}

/// Translates [`mir_ty::Ty`] to [`rty::Type`].
///
/// This struct implements a translation from Rust MIR types to Thrust types.
/// Thrust types may contain refinement predicates which do not exist in MIR types,
/// and [`TypeBuilder`] solely builds types with null refinement (true) in
/// [`TypeBuilder::build`]. This also provides [`TypeBuilder::for_template`] to build
/// refinement types by filling unknown predicates with templates with predicate variables.
#[derive(Clone)]
pub struct TypeBuilder<'tcx> {
    tcx: mir_ty::TyCtxt<'tcx>,
    def_ids: DefIdCache<'tcx>,
    owner_fn_id: DefId,
    typing_env: mir_ty::TypingEnv<'tcx>,
    /// Maps index in [`mir_ty::ParamTy`] to [`rty::TypeParamIdx`].
    /// These indices may differ because we skip lifetime parameters and they always need to be
    /// mapped when we translate a [`mir_ty::ParamTy`] to [`rty::ParamType`].
    /// See [`rty::TypeParamIdx`] for more details.
    param_idx_mapping: HashMap<u32, rty::TypeParamIdx>,
    type_params: Rc<RefCell<TypeParamMap<'tcx>>>,
    closure_type_params: Rc<RefCell<HashMap<TypeParam, rty::FunctionType>>>,
    system: Rc<RefCell<chc::System>>,
}

// TODO: Fold `TypeBuilder::closure_trait_ret` into `closure_trait_call` so that one function
// resolves a closure-typed parameter's whole call signature instead of two halves reporting the
// parameters and the return type separately.
/// What a `Fn`/`FnMut`/`FnOnce` bound says about calling a closure-typed parameter: the parameters
/// of the call, and which of the three traits the bound is. The return type comes separately, from
/// [`TypeBuilder::closure_trait_ret`].
struct ClosureTraitCall {
    params: IndexVec<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
    kind: mir_ty::ClosureKind,
}

/// The sort a closure precondition takes its upvars in.
///
/// An `FnMut` closure receives its upvars behind a `&mut`, whose prophecy is still unconstrained
/// where the precondition has to be discharged; the precondition therefore names their current
/// value rather than the `Mut` pair. `Fn` and `FnOnce` carry no prophecy to drop.
fn pre_upvars_sort(upvars: chc::Sort, closure_kind: mir_ty::ClosureKind) -> chc::Sort {
    match closure_kind {
        mir_ty::ClosureKind::FnMut => upvars.deref(),
        mir_ty::ClosureKind::Fn | mir_ty::ClosureKind::FnOnce => upvars,
    }
}

/// The upvars term matching [`pre_upvars_sort`].
fn pre_upvars_term<V>(upvars: chc::Term<V>, closure_kind: mir_ty::ClosureKind) -> chc::Term<V> {
    match closure_kind {
        mir_ty::ClosureKind::FnMut => upvars.mut_current(),
        mir_ty::ClosureKind::Fn | mir_ty::ClosureKind::FnOnce => upvars,
    }
}

impl<'tcx> TypeBuilder<'tcx> {
    pub fn new(
        tcx: mir_ty::TyCtxt<'tcx>,
        def_ids: DefIdCache<'tcx>,
        owner_fn_id: DefId,
        type_params: Rc<RefCell<TypeParamMap<'tcx>>>,
        closure_type_params: Rc<RefCell<HashMap<TypeParam, rty::FunctionType>>>,
        system: Rc<RefCell<chc::System>>,
    ) -> Self {
        let generics = tcx.generics_of(owner_fn_id);
        let mut param_idx_mapping: HashMap<u32, rty::TypeParamIdx> = Default::default();
        for i in 0..generics.count() {
            let generic_param = generics.param_at(i, tcx);
            match generic_param.kind {
                mir_ty::GenericParamDefKind::Lifetime => {}
                mir_ty::GenericParamDefKind::Type { .. } => {
                    param_idx_mapping.insert(i as u32, param_idx_mapping.len().into());
                }
                mir_ty::GenericParamDefKind::Const { .. } => {}
            }
        }

        tracing::debug!("TypeBuilder is created for {owner_fn_id:?} with param_idx_mapping {param_idx_mapping:#?}.");
        let typing_env = mir_ty::TypingEnv::post_analysis(tcx, owner_fn_id);
        Self {
            tcx,
            def_ids,
            owner_fn_id,
            typing_env,
            param_idx_mapping,
            type_params,
            closure_type_params,
            system,
        }
    }

    pub fn owner_fn_id(&self) -> DefId {
        self.owner_fn_id
    }

    /// Returns the def_id of the declaration site of the given type parameter.
    ///
    /// For impl methods, an inherited parameter (e.g. the impl's `I`) reports
    /// the def_id of the parameter declared on the impl block, so all uses
    /// of that parameter across the impl's methods share a single cache key.
    pub fn param_def_id(&self, ty: &mir_ty::ParamTy) -> DefId {
        let generics = self.tcx.generics_of(self.owner_fn_id);
        generics.param_at(ty.index as usize, self.tcx).def_id
    }

    /// Returns the local index of a type parameter within the declaring item,
    /// skipping lifetime and const parameters. This is the position used for
    /// monomorphization of generic arguments.
    pub fn param_local_idx(&self, ty: &mir_ty::ParamTy) -> u32 {
        let idx = self
            .param_idx_mapping
            .get(&ty.index)
            .expect("unknown type param idx");
        u32::from(*idx)
    }

    fn translate_param_type(&self, ty: &mir_ty::ParamTy) -> rty::Type<rty::Closed> {
        // FIXME:
        // `__ThrustSelf` is currently treated as a distinct `ParamTy` from `Self`,
        // which can lead to cache/key mismatches (e.g. in `TypeParamMap`).
        //
        // We currently normalize it here as a workaround, but this should be done
        // earlier during type translation/analysis so that all internal
        // representations consistently use the canonical `Self` parameter.
        if ty.name.as_str() == "__ThrustSelf" {
            let parent_def_id = self.tcx.parent(self.owner_fn_id);
            let self_ty_def = self
                .tcx
                .generics_of(parent_def_id)
                .own_params
                .iter()
                .find(|ty| ty.name.as_str() == "Self")
                .expect("Type parameter `Self` is not found.");

            let self_ty = mir_ty::ParamTy::new(self_ty_def.index, self_ty_def.name);
            tracing::debug!("replace {ty:?} with {self_ty:?}.");
            return self.translate_param_type(&self_ty);
        }
        let param_local_idx = self.param_local_idx(ty);

        let param_def_id = self.param_def_id(ty);
        tracing::debug!("translating ParamTy {ty:?} (decl={param_def_id:?})...");

        let mut type_params = self.type_params.borrow_mut();
        let forall_sort_idx = type_params
            .entry(TypeParam::GenericType {
                param_def_id,
                local_idx: param_local_idx,
            })
            .or_insert_with(|| {
                let desc = format!("ParamTy {:?} (decl={:?})", ty, param_def_id);
                let debug_info = chc::DebugInfo::default().with_context("type_param", desc.clone());
                let idx = self.system.borrow_mut().new_forall_sort(debug_info);
                tracing::debug!("issue the new ForallSortIdx {} for {desc}.", idx);
                idx
            });
        rty::ParamType::new(rty::TypeParamIdx::from(param_local_idx), *forall_sort_idx).into()
    }

    fn translate_alias_type(&self, ty: &mir_ty::AliasTy<'tcx>) -> rty::Type<rty::Closed> {
        let projection = mir_ty::Ty::new_projection(self.tcx, ty.def_id, ty.args);
        if let Ok(normalized) = self
            .tcx
            .try_normalize_erasing_regions(self.typing_env, projection)
        {
            if normalized != projection {
                tracing::debug!(
                    "alias projection {:#?} normalized to {:#?}",
                    projection,
                    normalized
                );
                return self.build(normalized);
            }
        }

        let args: Vec<rty::Type<rty::Closed>> = ty.args.types().map(|t| self.build(t)).collect();
        let mut type_params = self.type_params.borrow_mut();
        tracing::debug!(?type_params);
        let index = type_params
            .entry(TypeParam::AssocType(ty.def_id, args.clone()))
            .or_insert_with(|| {
                let desc = format!(
                    "AliasTy {:?} with (def_id = {:?}, args = {:?})",
                    ty, ty.def_id, args
                );
                let debug_info = chc::DebugInfo::default().with_context("type_param", desc.clone());
                let idx = self.system.borrow_mut().new_forall_sort(debug_info);
                tracing::debug!("issue the new ForallSortIdx {} for {desc}.", idx);
                idx
            });

        rty::AliasType::new(*index, args).into()
    }

    pub(crate) fn register_closure_type_param(
        &self,
        type_param: TypeParam,
        fun_type: rty::FunctionType,
    ) {
        tracing::info!(?type_param, ?fun_type, "register_closure_type_param");
        self.closure_type_params
            .borrow_mut()
            .insert(type_param, fun_type);
    }

    /// Replaces {closure} types with thrust_models::Closure<{closure}>.
    ///
    /// Ideally, we want to have `impl<F> Model for F where F: Fn` instead of this and let
    /// normalization do the work. However, it doesn't work:
    /// 1. it simply conflicts with other blanket impls
    /// 2. attempts to fake the impl via override_queries have failed so far
    fn replace_closure_model(&self, ty: mir_ty::Ty<'tcx>) -> mir_ty::Ty<'tcx> {
        let Some(closure_model_id) = self.def_ids.closure_model() else {
            return ty;
        };

        struct ReplaceClosureModel<'tcx> {
            tcx: mir_ty::TyCtxt<'tcx>,
            closure_model_id: DefId,
        }

        use mir_ty::TypeFoldable;
        impl<'tcx> mir_ty::TypeFolder<mir_ty::TyCtxt<'tcx>> for ReplaceClosureModel<'tcx> {
            fn cx(&self) -> mir_ty::TyCtxt<'tcx> {
                self.tcx
            }

            fn fold_ty(&mut self, ty: mir_ty::Ty<'tcx>) -> mir_ty::Ty<'tcx> {
                use mir_ty::TypeSuperFoldable;
                if let mir_ty::TyKind::Closure(_, args) = ty.kind() {
                    let args = self
                        .tcx
                        .mk_args(&[args.as_closure().tupled_upvars_ty().into()]);
                    let adt_def = self.tcx.adt_def(self.closure_model_id);
                    return mir_ty::Ty::new_adt(self.tcx, adt_def, args);
                }
                ty.super_fold_with(self)
            }
        }

        ty.fold_with(&mut ReplaceClosureModel {
            tcx: self.tcx,
            closure_model_id,
        })
    }

    pub fn resolve_model_ty(&self, orig_ty: mir_ty::Ty<'tcx>) -> mir_ty::Ty<'tcx> {
        let ty = self.replace_closure_model(orig_ty);

        let Some(model_ty_def_id) = self.def_ids.model_ty() else {
            return ty;
        };
        let args = self.tcx.mk_args(&[ty.into()]);
        tracing::debug!("generic args are {:#?}.", args);
        let projection_ty = mir_ty::Ty::new_projection(self.tcx, model_ty_def_id, args);
        if let Ok(normalized_ty) = self
            .tcx
            .try_normalize_erasing_regions(self.typing_env, projection_ty)
        {
            tracing::debug!(
                "the type {:#?} is normalized as the type {:#?}.",
                orig_ty,
                normalized_ty
            );
            // A partly normalized result is still progress: `build` expands the
            // `Model::Ty` projections left inside it. Only a result that still
            // projects `ty` itself has to be rejected, or `build` would come back here.
            let stuck_on_ty = normalized_ty.walk().any(|arg| {
                if let mir_ty::GenericArgKind::Type(t) = arg.kind() {
                    matches!(
                        t.kind(),
                        mir_ty::TyKind::Alias(_, alias_ty)
                            if alias_ty.def_id == model_ty_def_id && alias_ty.args.type_at(0) == ty
                    )
                } else {
                    false
                }
            });
            if !stuck_on_ty {
                return normalized_ty;
            }
        }
        tracing::debug!("the type {:#?} is replaced as the {:#?}.", orig_ty, ty);
        ty
    }

    // TODO: consolidate two impls
    fn model_adt(
        &self,
        adt: &mir_ty::AdtDef<'tcx>,
        args: &'tcx mir_ty::List<mir_ty::GenericArg<'tcx>>,
    ) -> Option<rty::Type<rty::Closed>> {
        if Some(adt.did()) == self.def_ids.int_model() {
            return Some(rty::Type::int());
        }

        if Some(adt.did()) == self.def_ids.mut_model() {
            let elem_ty = self.build(args.type_at(0));
            return Some(rty::PointerType::mut_to(elem_ty).into());
        }

        if Some(adt.did()) == self.def_ids.box_model() {
            let elem_ty = self.build(args.type_at(0));
            return Some(rty::PointerType::own(elem_ty).into());
        }

        if Some(adt.did()) == self.def_ids.seq_model() {
            let elem_ty = self.build(args.type_at(0));
            return Some(rty::Type::Seq(Box::new(rty::RefinedType::unrefined(
                elem_ty,
            ))));
        }

        if Some(adt.did()) == self.def_ids.array_model() {
            let idx_ty = self.build(args.type_at(0));
            let elem_ty = self.build(args.type_at(1));
            return Some(rty::ArrayType::new(idx_ty, elem_ty).into());
        }

        if Some(adt.did()) == self.def_ids.closure_model() {
            let tupled_upvars_ty = args.type_at(0);
            return Some(self.build(tupled_upvars_ty));
        }

        // TODO: keep this in step with `impl<T: Model> Model for Ghost<T>` in std.rs, which
        // resolves a `Ghost<T>` to its content as well.
        //
        // Which of the two applies is not evident from the source: a concrete `Ghost<i64>`
        // normalizes and never reaches here, while a generic one does, because
        // `resolve_model_ty` either fails to normalize it or discards the partly normalized
        // result. See that impl for why it cannot be a fixed point like the models above.
        if Some(adt.did()) == self.def_ids.ghost_model() {
            let content_ty = args.type_at(0);
            return Some(self.build(content_ty));
        }

        None
    }

    // TODO: consolidate two impls
    pub fn build(&self, ty: mir_ty::Ty<'tcx>) -> rty::Type<rty::Closed> {
        let ty = self.resolve_model_ty(ty);
        match ty.kind() {
            mir_ty::TyKind::Bool => rty::Type::bool(),
            mir_ty::TyKind::Str => rty::Type::string(),
            mir_ty::TyKind::Ref(_, elem_ty, mir_ty::Mutability::Not) => {
                let elem_ty = self.build(*elem_ty);
                rty::PointerType::immut_to(elem_ty).into()
            }
            mir_ty::TyKind::Ref(_, elem_ty, mir_ty::Mutability::Mut) => {
                let elem_ty = self.build(*elem_ty);
                rty::PointerType::mut_to(elem_ty).into()
            }
            mir_ty::TyKind::Tuple(ts) => {
                // elaboration: all fields are boxed
                let elems = ts
                    .iter()
                    .map(|ty| rty::PointerType::own(self.build(ty)).into())
                    .collect();
                rty::TupleType::new(elems).into()
            }
            mir_ty::TyKind::Never => rty::Type::never(),
            mir_ty::TyKind::Param(ty) => self.translate_param_type(ty),
            mir_ty::TyKind::FnPtr(sig_tys, hdr) => {
                // TODO: justification for skip_binder
                let sig = sig_tys.with(*hdr).skip_binder();
                let params = sig
                    .inputs()
                    .iter()
                    .map(|ty| rty::RefinedType::unrefined(self.build(*ty)).vacuous())
                    .collect();
                let ret = rty::RefinedType::unrefined(self.build(sig.output()));
                rty::FunctionType::new(params, ret.vacuous()).into()
            }
            mir_ty::TyKind::Slice(elem_ty) | mir_ty::TyKind::Array(elem_ty, _) => {
                let elem_ty = self.build(*elem_ty);
                seq_model_type(elem_ty)
            }
            mir_ty::TyKind::Adt(def, params) => {
                if let Some(model_ty) = self.model_adt(def, params) {
                    return model_ty;
                }
                // Treat Box and Vec as opaque types to avoid traversing internal structure
                if Some(def.did()) == self.def_ids.box_() {
                    let elem_ty = self.build(params.type_at(0));
                    return rty::PointerType::own(elem_ty).into();
                }
                if Some(def.did()) == self.def_ids.vec() {
                    let elem_ty = self.build(params.type_at(0));
                    return seq_model_type(elem_ty);
                }
                if Some(def.did()) == self.def_ids.slice_iter()
                    || Some(def.did()) == self.def_ids.vec_into_iter()
                {
                    let elem_ty = self.build(iterated_elem_ty(ty, params));
                    return seq_iter_model_type(seq_model_type(elem_ty));
                }
                if Some(def.did()) == self.def_ids.slice_iter_mut() {
                    let elem_ty = self.build(iterated_elem_ty(ty, params));
                    return mut_seq_iter_model_type(seq_model_type(elem_ty));
                }
                if def.is_enum() {
                    let sym = refine::datatype_symbol(self.tcx, def.did());
                    let args: IndexVec<_, _> = params
                        .types()
                        .map(|ty| rty::RefinedType::unrefined(self.build(ty)))
                        .collect();
                    rty::EnumType::new(sym, args).into()
                } else if def.is_struct() {
                    let elem_tys = def
                        .all_fields()
                        .map(|field| {
                            let ty = field.ty(self.tcx, params);
                            // elaboration: all fields are boxed
                            rty::PointerType::own(self.build(ty)).into()
                        })
                        .collect();
                    rty::TupleType::new(elem_tys).into()
                } else {
                    unimplemented!("unsupported ADT: {:?}", ty);
                }
            }
            mir_ty::TyKind::Alias(mir_ty::AliasTyKind::Projection, ty) => {
                if let Some(model_ty_def_id) = self.def_ids.model_ty() {
                    let arg_ty = ty.args.type_at(0);

                    if ty.def_id == model_ty_def_id
                        && (matches!(
                            arg_ty.kind(),
                            mir_ty::TyKind::Param(_) | mir_ty::TyKind::Alias(..)
                        ))
                    {
                        tracing::debug!(
                            "expanding projection to thrust_models::Model::Ty for {arg_ty:?}."
                        );
                        return self.build(arg_ty);
                    }
                }

                self.translate_alias_type(ty)
            }
            kind => unimplemented!("unrefined_ty: {:?}", kind),
        }
    }

    pub fn build_basic_block<I>(
        &mut self,
        body: &rustc_middle::mir::Body<'tcx>,
        live_locals: I,
        ret_ty: mir_ty::Ty<'tcx>,
    ) -> BasicBlockType
    where
        I: IntoIterator<Item = (Local, mir_ty::TypeAndMut<'tcx>)>,
    {
        struct FakeRegistry;
        impl TemplateRegistry for FakeRegistry {
            fn register_template<V>(&mut self, _tmpl: rty::Template<V>) -> rty::RefinedType<V> {
                panic!("unexpected template registration")
            }
        }
        self.for_template(&mut FakeRegistry)
            .build_basic_block_with_precondition(
                body,
                live_locals.into_iter().collect(),
                ret_ty,
                Some(rty::Refinement::top()),
            )
    }

    pub fn for_template<'a, R>(
        &self,
        registry: &'a mut R,
    ) -> TemplateTypeBuilder<'tcx, 'a, R, EmptyTemplateScope> {
        TemplateTypeBuilder {
            inner: self.clone(),
            registry,
            scope: Default::default(),
        }
    }

    pub fn for_function_template<'a, R>(
        &self,
        registry: &'a mut R,
        sig: mir_ty::FnSig<'tcx>,
    ) -> FunctionTemplateTypeBuilder<'tcx, 'a, R> {
        let abi = match sig.abi {
            rustc_abi::ExternAbi::Rust => rty::FunctionAbi::Rust,
            rustc_abi::ExternAbi::RustCall => rty::FunctionAbi::RustCall,
            _ => unimplemented!("unsupported function ABI: {:?}", sig.abi),
        };
        FunctionTemplateTypeBuilder {
            inner: self.clone(),
            registry,
            param_tys: sig
                .inputs()
                .iter()
                .map(|ty| mir_ty::TypeAndMut {
                    ty: *ty,
                    mutbl: Mutability::Not,
                })
                .collect(),
            ret_ty: sig.output(),
            param_rtys: Default::default(),
            param_refinement: None,
            ret_rty: None,
            abi,
        }
    }

    /// Extracts the [`ClosureTraitCall`] of a `Fn` / `FnMut` / `FnOnce` trait predicate
    /// whose `Self` type matches `param_ty`. Returns `None` otherwise.
    ///
    /// The first parameter is the closure value (wrapped in a `&` / `&mut` pointer
    /// for `Fn` / `FnMut`, or owned for `FnOnce`), followed by the logical arguments
    /// as a single tuple matching the call-site shape produced by
    /// `<F as Fn<(A,)>>::call(...)`.
    #[tracing::instrument(skip(self))]
    fn closure_trait_call(
        &self,
        param_ty: mir_ty::ParamTy,
        pred: mir_ty::TraitPredicate<'tcx>,
    ) -> Option<ClosureTraitCall> {
        let trait_ref = pred.trait_ref;
        if trait_ref.self_ty() != param_ty.to_ty(self.tcx) {
            return None;
        }
        // Reject non-`Fn`/`FnMut`/`FnOnce` predicates (e.g. `Sized`) before building any type,
        // so that a `ParamTy` the current TypeBuilder cannot translate is never built here.
        use mir_ty::ClosureKind::*;
        let closure_kind = self.tcx.fn_trait_kind_from_def_id(trait_ref.def_id)?;
        tracing::debug!(?trait_ref.args);

        let receiver_type = self.build(trait_ref.args.type_at(0));
        let receiver_type = match closure_kind {
            Fn => rty::PointerType::immut_to(receiver_type).into(),
            FnMut => rty::PointerType::mut_to(receiver_type).into(),
            FnOnce => receiver_type,
        };

        let mir_ty::Tuple(other_params) = trait_ref.args.type_at(1).kind() else {
            panic!("Closure should have at least one argument.")
        };

        let other_params = other_params.iter().map(|ty| self.build(ty).vacuous());
        let params = std::iter::once(receiver_type.vacuous())
            .chain(other_params)
            .map(rty::RefinedType::unrefined)
            .collect();

        tracing::debug!("found the signature for closure trait: {params:#?}");
        Some(ClosureTraitCall {
            params,
            kind: closure_kind,
        })
    }

    /// Extracts the return type refinement for `<F as FnOnce>::Output` projection
    /// where `F = param_ty`. Returns `None` otherwise.
    #[tracing::instrument(skip(self))]
    fn closure_trait_ret(
        &self,
        param_ty: mir_ty::ParamTy,
        pred: mir_ty::ProjectionPredicate<'tcx>,
    ) -> Option<rty::RefinedType<rty::FunctionParamIdx>> {
        let projection = pred.projection_term;
        if projection.def_id != self.tcx.lang_items().fn_once_output()?
            || projection.args.type_at(0) != param_ty.to_ty(self.tcx)
        {
            return None;
        }

        let ret_ty = self.build(pred.term.expect_type()).vacuous();
        tracing::debug!(?ret_ty);
        Some(rty::RefinedType::unrefined(ret_ty))
    }

    /// Builds the [`rty::FunctionType`] for a type parameter `param_ty` declared
    /// on the function identified by `local_def_id`, when `param_ty` is bounded
    /// by `Fn` / `FnMut` / `FnOnce`.
    ///
    /// `generic_args` are the generic arguments of the enclosing function
    /// (the function whose body is being type-checked). When the enclosing
    /// function is itself generic, `predicates_of(local_def_id)` is the raw
    /// predicate list which is then instantiated with `generic_args`. When
    /// `generic_args` is empty, predicates are used un-instantiated.
    ///
    /// Returns `None` if `param_ty` has no `Fn` / `FnMut` / `FnOnce` trait bound.
    /// As a side effect, the closure pre/post forall predicates are registered
    /// with the [`chc::System`].
    /// Resolves `param_ty`, declared by some other item, at the generic arguments
    /// this analysis runs with.
    ///
    /// Returns the type parameter those arguments map it to -- which is the one the
    /// current [`Self::param_local_idx`] can read -- or `None` when it maps to a
    /// concrete type, which carries its own contract and needs no parameter-keyed one.
    pub fn resolve_param_ty(
        &self,
        param_ty: mir_ty::ParamTy,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<mir_ty::ParamTy> {
        if generic_args.is_empty() {
            return Some(param_ty);
        }
        // Bind the *type*, not the `ParamTy`: instantiating a `ParamTy` can only ever
        // return a `ParamTy`, so it cannot substitute a concrete argument.
        let ty =
            mir_ty::EarlyBinder::bind(param_ty.to_ty(self.tcx)).instantiate(self.tcx, generic_args);
        match ty.kind() {
            mir_ty::TyKind::Param(p) => Some(*p),
            _ => None,
        }
    }

    /// Builds the contract of a closure-typed parameter from its `Fn` bound.
    ///
    /// `param_ty` must already be resolved for the current analysis
    /// ([`Self::resolve_param_ty`]); `generic_args` instantiates `local_def_id`'s
    /// predicates so the bound is found at those same arguments.
    pub fn build_closure_type_for_param(
        &self,
        param_ty: mir_ty::ParamTy,
        local_def_id: rustc_hir::def_id::LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<rty::FunctionType> {
        // `predicates_of(..).predicates` holds only the predicates written on the
        // function itself; a bound such as `F: FnMut(..)` on the enclosing impl or
        // trait lives in the parent's predicates. `instantiate` and
        // `instantiate_identity` walk the parent chain, so go through them.
        let generic_predicates = self.tcx.predicates_of(local_def_id.to_def_id());
        let predicates = if !generic_args.is_empty() {
            generic_predicates.instantiate(self.tcx, generic_args)
        } else {
            generic_predicates.instantiate_identity(self.tcx)
        };
        let mut predicates = predicates.predicates.into_iter();

        let ClosureTraitCall {
            mut params,
            kind: closure_kind,
        } = predicates.clone().find_map(|clause| {
            self.closure_trait_call(param_ty, clause.as_trait_clause()?.skip_binder())
        })?;
        let mut ret = predicates.find_map(|clause| {
            self.closure_trait_ret(param_ty, clause.as_projection_clause()?.skip_binder())
        })?;

        let free = |idx| chc::Term::var(rty::RefinedTypeVar::Free(idx));
        let value = chc::Term::var(rty::RefinedTypeVar::Value);

        let args: Vec<_> = params
            .iter()
            .enumerate()
            .map(|(idx, _)| free(rty::FunctionParamIdx::from_usize(idx)))
            .collect();

        let type_params = vec![self.build(param_ty.to_ty(self.tcx)).to_sort()];
        let mut params_sort: Vec<chc::Sort> = params.iter().map(|rty| rty.ty.to_sort()).collect();
        let ret_sort = ret.ty.to_sort();

        let mut pre_params_sort = params_sort.clone();
        pre_params_sort[0] = pre_upvars_sort(pre_params_sort[0].clone(), closure_kind);

        let pre_pred = refine::closure_pre_forall_pred(
            self.tcx,
            self.owner_fn_id,
            type_params.clone(),
            pre_params_sort,
        );
        self.system
            .borrow_mut()
            .register_forall_pred(pre_pred.clone());
        params_sort.push(ret_sort);
        let post_pred =
            refine::closure_post_forall_pred(self.tcx, self.owner_fn_id, type_params, params_sort);
        self.system
            .borrow_mut()
            .register_forall_pred(post_pred.clone());

        params
            .iter_mut()
            .last()
            .expect("Closure should have at least one argument.")
            .extend_refinement({
                // This refinement rides on the closure's last parameter, so `value` names that
                // parameter here and `free(idx)` the earlier ones: a closure taking no logical
                // argument has its upvars in the `value` slot.
                let (args_front, _args_last) = args.split_at(args.len() - 1);
                let mut pre_args: Vec<_> =
                    [args_front, std::slice::from_ref(&value.clone())].concat();
                pre_args[0] = pre_upvars_term(pre_args[0].clone(), closure_kind);
                chc::Atom::new(pre_pred.into(), pre_args).into()
            });

        ret.extend_refinement(
            chc::Atom::new(post_pred.into(), [args, vec![value.clone()]].concat()).into(),
        );
        let ret = Box::new(ret);

        Some(rty::FunctionType {
            params,
            ret,
            abi: rty::FunctionAbi::RustCall,
        })
    }
}

/// Translates [`mir_ty::Ty`] to [`rty::Type`] using templates for refinements.
///
/// [`rty::Template`] is a refinement type in the form of `{ T | P(x1, ..., xn) }` where `P` is a
/// predicate variable. When constructing a template, we need to know which variables can affect the
/// predicate of the template (dependencies, `x1, ..., xn`), and they are provided by the
/// [`TemplateScope`]. No variables are in scope by default and you can provide a scope using
/// [`TemplateTypeBuilder::with_scope`].
pub struct TemplateTypeBuilder<'tcx, 'a, R, S> {
    inner: TypeBuilder<'tcx>,
    // XXX: this can't be simply `R` because monomorphization instantiates types recursively
    registry: &'a mut R,
    scope: S,
}

impl<'tcx, 'a, R, S> TemplateTypeBuilder<'tcx, 'a, R, S> {
    pub fn with_scope<T>(self, scope: T) -> TemplateTypeBuilder<'tcx, 'a, R, T> {
        TemplateTypeBuilder {
            inner: self.inner,
            registry: self.registry,
            scope,
        }
    }
}

impl<'tcx, 'a, R, S> TemplateTypeBuilder<'tcx, 'a, R, S>
where
    R: TemplateRegistry,
    S: TemplateScope,
{
    fn model_adt(
        &mut self,
        adt: &mir_ty::AdtDef<'tcx>,
        args: &'tcx mir_ty::List<mir_ty::GenericArg<'tcx>>,
    ) -> Option<rty::Type<S::Var>> {
        if Some(adt.did()) == self.inner.def_ids.int_model() {
            return Some(rty::Type::int());
        }

        if Some(adt.did()) == self.inner.def_ids.mut_model() {
            let elem_ty = self.build(args.type_at(0));
            return Some(rty::PointerType::mut_to(elem_ty).into());
        }

        if Some(adt.did()) == self.inner.def_ids.box_model() {
            let elem_ty = self.build(args.type_at(0));
            return Some(rty::PointerType::own(elem_ty).into());
        }

        if Some(adt.did()) == self.inner.def_ids.seq_model() {
            let elem_ty = self.build(args.type_at(0));
            return Some(rty::Type::Seq(Box::new(rty::RefinedType::unrefined(
                elem_ty,
            ))));
        }

        if Some(adt.did()) == self.inner.def_ids.array_model() {
            let idx_ty = self.build(args.type_at(0));
            let elem_ty = self.build(args.type_at(1));
            return Some(rty::ArrayType::new(idx_ty, elem_ty).into());
        }

        if Some(adt.did()) == self.inner.def_ids.closure_model() {
            let tupled_upvars_ty = args.type_at(0);
            return Some(self.build(tupled_upvars_ty));
        }

        // TODO: keep in step with `impl Model for Ghost` in std.rs; see
        // `TypeBuilder::model_adt`.
        if Some(adt.did()) == self.inner.def_ids.ghost_model() {
            let content_ty = args.type_at(0);
            return Some(self.build(content_ty));
        }

        None
    }

    pub fn build(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::Type<S::Var> {
        let ty = self.inner.resolve_model_ty(ty);
        match ty.kind() {
            mir_ty::TyKind::Bool => rty::Type::bool(),
            mir_ty::TyKind::Str => rty::Type::string(),
            mir_ty::TyKind::Ref(_, elem_ty, mir_ty::Mutability::Not) => {
                let elem_ty = self.build(*elem_ty);
                rty::PointerType::immut_to(elem_ty).into()
            }
            mir_ty::TyKind::Ref(_, elem_ty, mir_ty::Mutability::Mut) => {
                let elem_ty = self.build(*elem_ty);
                rty::PointerType::mut_to(elem_ty).into()
            }
            mir_ty::TyKind::Tuple(ts) => {
                // elaboration: all fields are boxed
                let elems = ts
                    .iter()
                    .map(|ty| rty::PointerType::own(self.build(ty)).into())
                    .collect();
                rty::TupleType::new(elems).into()
            }
            mir_ty::TyKind::Never => rty::Type::never(),
            mir_ty::TyKind::Param(ty) => self.inner.translate_param_type(ty).vacuous(),
            mir_ty::TyKind::FnPtr(sig_tys, hdr) => {
                // TODO: justification for skip_binder
                let sig = sig_tys.with(*hdr).skip_binder();
                let ty = self.inner.for_function_template(self.registry, sig).build();
                rty::Type::function(ty)
            }
            mir_ty::TyKind::Slice(elem_ty) | mir_ty::TyKind::Array(elem_ty, _) => {
                let elem_ty = self.build(*elem_ty);
                seq_model_type(elem_ty)
            }
            mir_ty::TyKind::Adt(def, params) => {
                if let Some(model_ty) = self.model_adt(def, params) {
                    return model_ty;
                }
                // Treat Box and Vec as opaque types to avoid traversing internal structure
                if Some(def.did()) == self.inner.def_ids.box_() {
                    let elem_ty = self.build(params.type_at(0));
                    return rty::PointerType::own(elem_ty).into();
                }
                if Some(def.did()) == self.inner.def_ids.vec() {
                    let elem_ty = self.build(params.type_at(0));
                    return seq_model_type(elem_ty);
                }
                if Some(def.did()) == self.inner.def_ids.slice_iter()
                    || Some(def.did()) == self.inner.def_ids.vec_into_iter()
                {
                    let elem_ty = self.build(iterated_elem_ty(ty, params));
                    return seq_iter_model_type(seq_model_type(elem_ty));
                }
                if Some(def.did()) == self.inner.def_ids.slice_iter_mut() {
                    let elem_ty = self.build(iterated_elem_ty(ty, params));
                    return mut_seq_iter_model_type(seq_model_type(elem_ty));
                }
                if def.is_enum() {
                    let sym = refine::datatype_symbol(self.inner.tcx, def.did());
                    let args: IndexVec<_, _> =
                        params.types().map(|ty| self.build_refined(ty)).collect();
                    rty::EnumType::new(sym, args).into()
                } else if def.is_struct() {
                    let elem_tys = def
                        .all_fields()
                        .map(|field| {
                            let ty = field.ty(self.inner.tcx, params);
                            // elaboration: all fields are boxed
                            rty::PointerType::own(self.build(ty)).into()
                        })
                        .collect();
                    rty::TupleType::new(elem_tys).into()
                } else {
                    unimplemented!("unsupported ADT: {:?}", ty);
                }
            }
            mir_ty::TyKind::Alias(mir_ty::AliasTyKind::Projection, ty) => {
                if let Some(model_ty_def_id) = self.inner.def_ids.model_ty() {
                    let arg_ty = ty.args.type_at(0);

                    if ty.def_id == model_ty_def_id
                        && (matches!(
                            arg_ty.kind(),
                            mir_ty::TyKind::Param(_) | mir_ty::TyKind::Alias(..)
                        ))
                    {
                        tracing::debug!(
                            "expanding projection to thrust_models::Model::Ty for {arg_ty:?}."
                        );
                        return self.build(arg_ty);
                    }
                }

                self.inner.translate_alias_type(ty).vacuous()
            }
            kind => unimplemented!("ty: {:?}", kind),
        }
    }

    pub fn build_refined(&mut self, ty: mir_ty::Ty<'tcx>) -> rty::RefinedType<S::Var> {
        // TODO: consider building ty with scope
        let ty = self.inner.for_template(self.registry).build(ty).vacuous();
        let tmpl = self.scope.build_template().build(ty);
        self.registry.register_template(tmpl)
    }

    fn build_basic_block_with_precondition(
        &mut self,
        body: &rustc_middle::mir::Body<'tcx>,
        mut live_locals: Vec<(Local, mir_ty::TypeAndMut<'tcx>)>,
        ret_ty: mir_ty::Ty<'tcx>,
        precondition: Option<rty::Refinement<rty::FunctionParamIdx>>,
    ) -> BasicBlockType {
        // this is necessary for local_def::Analyzer::elaborate_unused_args
        live_locals.sort_by_key(|(local, _)| *local);

        let mut locals = IndexVec::<rty::FunctionParamIdx, _>::new();
        let mut tys = Vec::new();
        for (local, ty) in live_locals {
            locals.push((local, ty.mutbl));
            tys.push(ty);
        }

        for arg in body.args_iter() {
            let decl = &body.local_decls[arg];
            tys.push(mir_ty::TypeAndMut {
                ty: decl.ty,
                mutbl: decl.mutability,
            });
        }

        let ty = FunctionTemplateTypeBuilder {
            inner: self.inner.clone(),
            registry: self.registry,
            param_tys: tys,
            ret_ty,
            param_rtys: Default::default(),
            param_refinement: precondition,
            // not generating pvar of BB post
            ret_rty: Some(rty::RefinedType::unrefined(
                self.inner.build(ret_ty).vacuous(),
            )),
            abi: Default::default(),
        }
        .build();
        BasicBlockType {
            ty,
            locals,
            outer_fn_param_count: body.arg_count,
        }
    }

    pub fn build_basic_block<I>(
        &mut self,
        body: &rustc_middle::mir::Body<'tcx>,
        live_locals: I,
        ret_ty: mir_ty::Ty<'tcx>,
    ) -> BasicBlockType
    where
        I: IntoIterator<Item = (Local, mir_ty::TypeAndMut<'tcx>)>,
    {
        self.build_basic_block_with_precondition(
            body,
            live_locals.into_iter().collect(),
            ret_ty,
            None,
        )
    }
}

/// A builder for function template types.
pub struct FunctionTemplateTypeBuilder<'tcx, 'a, R> {
    inner: TypeBuilder<'tcx>,
    registry: &'a mut R,
    param_tys: Vec<mir_ty::TypeAndMut<'tcx>>,
    ret_ty: mir_ty::Ty<'tcx>,
    param_refinement: Option<rty::Refinement<rty::FunctionParamIdx>>,
    param_rtys: HashMap<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
    ret_rty: Option<rty::RefinedType<rty::FunctionParamIdx>>,
    abi: rty::FunctionAbi,
}

impl<'tcx, 'a, R> FunctionTemplateTypeBuilder<'tcx, 'a, R> {
    pub fn param_refinement(
        &mut self,
        refinement: rty::Refinement<rty::FunctionParamIdx>,
    ) -> &mut Self {
        let rty::Refinement { existentials, body } = refinement;
        let refinement = rty::Refinement {
            existentials,
            body: body.map_var(|v| match v {
                rty::RefinedTypeVar::Free(idx) if idx.index() == self.param_tys.len() - 1 => {
                    rty::RefinedTypeVar::Value
                }
                v => v,
            }),
        };
        self.param_refinement = Some(refinement);
        self
    }

    pub fn ret_refinement(
        &mut self,
        refinement: rty::Refinement<rty::FunctionParamIdx>,
    ) -> &mut Self {
        let ty = self.inner.build(self.ret_ty);
        self.ret_rty = Some(rty::RefinedType::new(ty.vacuous(), refinement));
        self
    }

    /// Records a refinement to install at a [`rty::TypePosition`].
    ///
    /// The first step must be [`rty::TypePositionStep::Param`] or
    /// [`rty::TypePositionStep::Return`]; the remaining steps are forwarded to
    /// [`rty::RefinedType::install_refinement_at`].
    pub fn refinement_at(
        &mut self,
        position: &rty::TypePosition,
        refinement: rty::Refinement<rty::FunctionParamIdx>,
    ) -> &mut Self {
        let (first, rest) = match position.steps().split_first() {
            Some(pair) => pair,
            None => panic!("type position applied to a function type must not be empty"),
        };
        match first {
            rty::TypePositionStep::Param(idx) => {
                if !self.param_rtys.contains_key(idx) {
                    let ty = self.inner.build(self.param_tys[idx.index()].ty).vacuous();
                    self.param_rtys
                        .insert(*idx, rty::RefinedType::unrefined(ty));
                }
                self.param_rtys
                    .get_mut(idx)
                    .unwrap()
                    .install_refinement_at(rest, refinement);
            }
            rty::TypePositionStep::Return => {
                if self.ret_rty.is_none() {
                    let ty = self.inner.build(self.ret_ty).vacuous();
                    self.ret_rty = Some(rty::RefinedType::unrefined(ty));
                }
                self.ret_rty
                    .as_mut()
                    .unwrap()
                    .install_refinement_at(rest, refinement);
            }
            rty::TypePositionStep::TypeArg(_) => {
                panic!("type position applied to a function type must start with a param or result step, not a type argument");
            }
        }
        self
    }
}

impl<'tcx, 'a, R> FunctionTemplateTypeBuilder<'tcx, 'a, R>
where
    R: TemplateRegistry,
{
    pub fn build(&mut self) -> rty::FunctionType {
        let mut builder = rty::TemplateBuilder::default();
        let mut param_rtys = IndexVec::<rty::FunctionParamIdx, _>::new();
        for (idx, param_ty) in self.param_tys.iter().enumerate() {
            let param_rty = self
                .param_rtys
                .get(&idx.into())
                .cloned()
                .unwrap_or_else(|| {
                    if idx == self.param_tys.len() - 1 {
                        if let Some(param_refinement) = &self.param_refinement {
                            let ty = self.inner.build(param_ty.ty);
                            rty::RefinedType::new(ty.vacuous(), param_refinement.clone())
                        } else {
                            self.inner
                                .for_template(self.registry)
                                .with_scope(&builder)
                                .build_refined(param_ty.ty)
                        }
                    } else if self.param_refinement.is_some() {
                        rty::RefinedType::unrefined(self.inner.build(param_ty.ty).vacuous())
                    } else {
                        rty::RefinedType::unrefined(
                            self.inner
                                .for_template(self.registry)
                                .build(param_ty.ty)
                                .vacuous(),
                        )
                    }
                });
            let param_rty = if param_ty.mutbl.is_mut() {
                // elaboration: treat mutabully declared variables as own
                param_rty.boxed()
            } else {
                param_rty
            };
            let param_sort = param_rty.ty.to_sort();
            let param_idx = param_rtys.push(param_rty);
            builder.add_dependency(param_idx, param_sort);
        }

        // elaboration: we need at least one predicate variable in parameter
        if self.param_tys.is_empty() {
            let param_rty = if let Some(param_refinement) = &self.param_refinement {
                rty::RefinedType::new(rty::Type::unit(), param_refinement.clone())
            } else {
                let unit_ty = self.inner.tcx.types.unit;
                self.inner
                    .for_template(self.registry)
                    .with_scope(&builder)
                    .build_refined(unit_ty)
            };
            param_rtys.push(param_rty);
        }

        let ret_rty = self.ret_rty.clone().unwrap_or_else(|| {
            self.inner
                .for_template(self.registry)
                .with_scope(&builder)
                .build_refined(self.ret_ty)
        });
        rty::FunctionType::new(param_rtys, ret_rty).with_abi(self.abi)
    }
}
