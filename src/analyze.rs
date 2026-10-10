//! Analysis of Rust MIR to generate a CHC system.
//!
//! The [`Analyzer`] generates subtyping constraints in the form of CHCs ([`chc::System`]).
//! The entry point is [`crate_::Analyzer::run`], followed by [`local_def::Analyzer::run`]
//! and [`basic_block::Analyzer::run`], while accumulating the necessary information in
//! [`Analyzer`]. Once [`chc::System`] is collected for the entire input, it invokes an external
//! CHC solver with the [`Analyzer::solve`] and subsequently reports the result.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

use num_bigint::BigInt;
use rustc_hir::lang_items::LangItem;
use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::Symbol;

use crate::analyze;
use crate::chc::{self, ForallSortIdx};
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{self, BasicBlockType, TypeBuilder};
use crate::rty;

mod annot;
mod annot_fn;
mod basic_block;
mod closure_hist_inv;
mod crate_;
mod did_cache;
mod local_def;
mod pred_inst;
mod reconstruct_slice_indexing;

// TODO: organize structure and remove cross dependency between refine
pub use did_cache::DefIdCache;

fn scalar_const_term<T>(
    ty: mir_ty::Ty<'_>,
    val: &mir::ConstValue,
) -> Option<(rty::Type<T>, chc::Term<T>)> {
    use mir::interpret::Scalar;
    match (ty.kind(), val) {
        (mir_ty::TyKind::Int(_), mir::ConstValue::Scalar(Scalar::Int(v))) => Some((
            rty::Type::int_of_width(v.size().bits() as u32),
            chc::Term::int(v.to_int(v.size())),
        )),
        (mir_ty::TyKind::Uint(_), mir::ConstValue::Scalar(Scalar::Int(v))) => Some((
            rty::Type::uint_of_width(v.size().bits() as u32),
            chc::Term::int(v.to_uint(v.size())),
        )),
        (mir_ty::TyKind::Bool, mir::ConstValue::Scalar(Scalar::Int(v))) => {
            Some((rty::Type::bool(), chc::Term::bool(v.try_to_bool().unwrap())))
        }
        _ => None,
    }
}

fn fn_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: mir_ty::GenericArgsRef<'tcx>,
    span: rustc_span::Span,
) -> mir::Operand<'tcx> {
    mir::Operand::Constant(Box::new(mir::ConstOperand {
        span,
        user_ty: None,
        const_: mir::Const::Val(
            mir::ConstValue::ZeroSized,
            mir_ty::Ty::new_fn_def(tcx, def_id, args),
        ),
    }))
}

pub fn mir_borrowck_skip_formula_fn(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    local_def_id: rustc_span::def_id::LocalDefId,
) -> rustc_middle::query::queries::mir_borrowck::ProvidedValue<'_> {
    // TODO: unify impl with local_def::Analyzer
    // if the def is closure defined in formula_fn
    let root_def_id = tcx.typeck_root_def_id(local_def_id.to_def_id());
    let is_annotated_as_formula_fn = tcx
        .get_attrs_by_path(local_def_id.to_def_id(), &analyze::annot::formula_fn_path())
        .next()
        .is_some()
        || tcx
            .get_attrs_by_path(root_def_id, &analyze::annot::formula_fn_path())
            .next()
            .is_some();

    if is_annotated_as_formula_fn {
        tracing::debug!(?local_def_id, "skipping borrow check for formula fn");
        let dummy_result = rustc_middle::mir::ConcreteOpaqueTypes(Default::default());
        return Ok(tcx.arena.alloc(dummy_result));
    }

    (rustc_interface::DEFAULT_QUERY_PROVIDERS
        .queries
        .mir_borrowck)(tcx, local_def_id)
}

pub fn local_of_function_param(idx: rty::FunctionParamIdx) -> Local {
    Local::from(idx.index() + 1)
}

pub fn function_param_of_local(local: Local) -> rty::FunctionParamIdx {
    rty::FunctionParamIdx::from(local.as_usize() - 1)
}

fn discr_value<'tcx>(tcx: TyCtxt<'tcx>, discr: mir_ty::util::Discr<'tcx>) -> BigInt {
    let (size, signed) = discr.ty.int_size_and_signed(tcx);
    if signed {
        size.sign_extend(discr.val).into()
    } else {
        discr.val.into()
    }
}

pub struct ReplacePlacesVisitor<'tcx> {
    replacements: HashMap<(Local, &'tcx [mir::PlaceElem<'tcx>]), mir::Place<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> mir::visit::MutVisitor<'tcx> for ReplacePlacesVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_place(
        &mut self,
        place: &mut mir::Place<'tcx>,
        _: mir::visit::PlaceContext,
        _: mir::Location,
    ) {
        let proj = place.projection.as_slice();
        for i in 0..=proj.len() {
            if let Some(to) = self.replacements.get(&(place.local, &proj[0..i])) {
                place.local = to.local;
                place.projection = self.tcx.mk_place_elems_from_iter(
                    to.projection.iter().chain(proj.iter().skip(i).cloned()),
                );
                return;
            }
        }
    }
}

impl<'tcx> ReplacePlacesVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            replacements: Default::default(),
        }
    }

    pub fn with_replacement(
        tcx: TyCtxt<'tcx>,
        from: mir::Place<'tcx>,
        to: mir::Place<'tcx>,
    ) -> Self {
        let mut visitor = Self::new(tcx);
        visitor.add_replacement(from, to);
        visitor
    }

    pub fn add_replacement(&mut self, from: mir::Place<'tcx>, to: mir::Place<'tcx>) {
        self.replacements
            .insert((from.local, from.projection.as_slice()), to);
    }

    pub fn visit_statement(&mut self, stmt: &mut mir::Statement<'tcx>) {
        // dummy location
        mir::visit::MutVisitor::visit_statement(self, stmt, mir::Location::START);
    }

    pub fn visit_terminator(&mut self, term: &mut mir::Terminator<'tcx>) {
        // dummy location
        mir::visit::MutVisitor::visit_terminator(self, term, mir::Location::START);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeferredDefMode {
    Analyze,
    NoAnalyze,
}

impl DeferredDefMode {
    fn should_analyze(&self) -> bool {
        matches!(self, DeferredDefMode::Analyze)
    }
}

/// See [`Analyzer::reuse_fn_mut_generic`].
#[derive(Default)]
struct FnMutInstanceObligations {
    laws: Vec<chc::Clause>,
    pre: Vec<chc::Clause>,
    /// The defs an instance has used the contract of as instantiated.
    reused: HashSet<DefId>,
}

/// The type parameters in scope of `def_id` (its own or an enclosing item's) bounded by `FnMut`.
pub fn fn_mut_bounded_params(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<DefId> {
    let generics = tcx.generics_of(def_id);
    let predicates = tcx.predicates_of(def_id).instantiate_identity(tcx);
    predicates
        .predicates
        .iter()
        .filter_map(|clause| {
            let trait_ref = clause.as_trait_clause()?.skip_binder().trait_ref;
            if tcx.fn_trait_kind_from_def_id(trait_ref.def_id) != Some(mir_ty::ClosureKind::FnMut) {
                return None;
            }
            let mir_ty::TyKind::Param(param_ty) = trait_ref.self_ty().kind() else {
                return None;
            };
            Some(generics.type_param(*param_ty, tcx).def_id)
        })
        .collect()
}

/// Whether a type argument contains a closure of kind `FnMut`.
fn has_fn_mut_closure(generic_args: mir_ty::GenericArgsRef<'_>) -> bool {
    generic_args.types().any(|ty| {
        ty.walk().any(|arg| {
            arg.as_type().is_some_and(|ty| match ty.kind() {
                mir_ty::TyKind::Closure(_, args) => {
                    args.as_closure().kind() == mir_ty::ClosureKind::FnMut
                }
                _ => false,
            })
        })
    })
}

#[derive(Debug, Clone)]
struct DeferredDefTy<'tcx> {
    // the def that provides the spec (`expected_ty`). this is different from a key in defs when
    // the def is an extern_spec_fn (then it is the extern_spec_fn wrapper carrying the contract).
    local_def_id: LocalDefId,
    cache: Rc<RefCell<HashMap<InstantiationKey<'tcx>, rty::RefinedType>>>,
    mode: DeferredDefMode,
    // The target's generic arguments at the spec's own tail call (`None` when this def is
    // registered under its own def_id, not as an extern spec). The def_id key this is stored
    // under can be one shared blanket impl covering many instantiations of one of its type
    // parameters (`Vec<T, A>: Index<I>` for any `I: SliceIndex<[T]>` is one `index` def_id for
    // every `I`), while a spec written against it fixes that parameter to one concrete type
    // (`_extern_spec_vec_index` only ever calls it at `I = usize`). `def_ty_with_args` uses this
    // to refuse the spec's contract at a call whose actual `I` is not that one, rather than
    // handing every instantiation the `usize` one's contract.
    target_args: Option<mir_ty::GenericArgsRef<'tcx>>,
}

/// Binds the parameters of an extern spec function to the arguments of an actual call, by
/// matching `target_args` (the spec's own tail call, in the target's parameter space) against
/// `generic_args` (the actual call's instantiation of the same target).
///
/// A parameter of the spec occurring in `target_args` is one the spec generalizes over and takes
/// whatever the actual call has at that place. Anything else the spec fixed is covered only by
/// the same type: the spec's body was checked once, against that one instantiation, and only
/// handles it. Returns `None` when the call is not covered.
fn bind_spec_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    spec_def_id: LocalDefId,
    target_args: mir_ty::GenericArgsRef<'tcx>,
    generic_args: mir_ty::GenericArgsRef<'tcx>,
) -> Option<mir_ty::GenericArgsRef<'tcx>> {
    let mut bound = HashMap::new();
    for (spec_arg, actual_arg) in target_args.iter().zip(generic_args.iter()) {
        if !match_spec_arg(tcx, spec_arg, actual_arg, &mut bound) {
            return None;
        }
    }
    Some(mir_ty::GenericArgs::for_item(
        tcx,
        spec_def_id.to_def_id(),
        |param, _| match param.kind {
            mir_ty::GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
            _ => bound
                .get(&param.index)
                .copied()
                .unwrap_or_else(|| tcx.mk_param_from_def(param)),
        },
    ))
}

/// How a spec's bound stands at the arguments it was bound to, in a caller's environment.
enum SpecBound {
    Holds,
    /// The bound's self type is a type parameter or an unresolved projection of the caller.
    Assumed,
    Fails,
}

/// The bounds an extern spec puts on its type parameters by traits of its own, and the associated
/// types those fix. `Model` is left out: it is assumed of every type parameter.
fn is_spec_bound(clause: mir_ty::Clause<'_>, model_trait: DefId) -> bool {
    if clause.as_projection_clause().is_some() {
        return true;
    }
    clause.as_trait_clause().is_some_and(|clause| {
        let trait_def_id = clause.skip_binder().trait_ref.def_id;
        trait_def_id.is_local() && trait_def_id != model_trait
    })
}

/// Whether spec bounds (see [`is_spec_bound`]) hold in the environment of `caller_def_id`.
/// Returns those assumed, or the first that fails.
///
/// A spec stated through a trait (`I: IteratorSpec`) says nothing about a type that does not
/// implement it, so a call at such a type finds no specification. A bound whose self type is a
/// type parameter or an unresolved projection is assumed: the caller's contract is then verified
/// under it, and [`Analyzer::check_reused_spec_bounds`] checks it at each instance that reuses that
/// contract.
///
/// `Model` and its `PartialEq` are assumed of every type parameter of the caller, as a spec
/// assumes them of its own: they are what a bound like `usize: SliceIndexSpec<T>` needs of `T`.
fn classify_spec_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    clauses: impl IntoIterator<Item = mir_ty::Clause<'tcx>>,
    caller_def_id: DefId,
    model_ty: DefId,
) -> Result<Vec<mir_ty::Clause<'tcx>>, mir_ty::Clause<'tcx>> {
    use rustc_infer::infer::TyCtxtInferExt as _;

    let typing_env = model_assuming_env(tcx, caller_def_id, model_ty);
    let infcx = tcx.infer_ctxt().build(typing_env.typing_mode);
    let mut assumed = Vec::new();
    for clause in clauses {
        let bound = match clause.as_projection_clause() {
            Some(projection) => projection_bound(tcx, typing_env, projection.skip_binder()),
            None => trait_bound(tcx, &infcx, typing_env, clause),
        };
        match bound {
            SpecBound::Holds => {}
            SpecBound::Assumed => assumed.push(clause),
            SpecBound::Fails => return Err(clause),
        }
    }
    Ok(assumed)
}

fn trait_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    infcx: &rustc_infer::infer::InferCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    clause: mir_ty::Clause<'tcx>,
) -> SpecBound {
    use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;
    use rustc_trait_selection::traits::{Obligation, ObligationCause};

    let trait_ref = clause.as_trait_clause().unwrap().skip_binder().trait_ref;
    let Ok(trait_ref) = tcx.try_normalize_erasing_regions(typing_env, trait_ref) else {
        return SpecBound::Assumed;
    };
    let obligation = Obligation::new(
        tcx,
        ObligationCause::dummy(),
        typing_env.param_env,
        trait_ref,
    );
    if infcx.predicate_must_hold_modulo_regions(&obligation) {
        return SpecBound::Holds;
    }
    if matches!(
        trait_ref.self_ty().kind(),
        mir_ty::TyKind::Param(_) | mir_ty::TyKind::Alias(..)
    ) {
        SpecBound::Assumed
    } else {
        SpecBound::Fails
    }
}

/// Whether an associated type a spec's bound fixes (`R: IntoSliceIdx<I, [T], Output = usize>`)
/// is that type at the arguments the spec was bound to. A spec's contract is stated for the type it
/// fixes: at another one the target's result is not the one the contract describes. A projection
/// that stays unresolved is assumed, like a bound on a type parameter.
fn projection_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    projection: mir_ty::ProjectionPredicate<'tcx>,
) -> SpecBound {
    let normalize = |term| tcx.try_normalize_erasing_regions(typing_env, term).ok();
    let (Some(actual), Some(fixed)) = (
        normalize(projection.projection_term.to_term(tcx)),
        normalize(projection.term),
    ) else {
        return SpecBound::Assumed;
    };
    if actual == fixed {
        return SpecBound::Holds;
    }
    let unresolved = actual.as_type().is_some_and(|ty| {
        matches!(
            ty.kind(),
            mir_ty::TyKind::Param(_) | mir_ty::TyKind::Alias(..)
        )
    });
    if unresolved {
        SpecBound::Assumed
    } else {
        SpecBound::Fails
    }
}

/// The environment a predicate call in `owner_fn_id` is resolved in: the owner's own, with `Model`
/// assumed of its type parameters as a spec assumes it, so that a call on a concrete type is
/// resolved to the impl's predicate even when the impl needs `T: Model` of a type parameter `T`.
fn predicate_typing_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner_fn_id: DefId,
    model_ty: Option<DefId>,
) -> mir_ty::TypingEnv<'tcx> {
    match model_ty {
        Some(model_ty) => model_assuming_env(tcx, owner_fn_id, model_ty),
        None => mir_ty::TypingEnv::post_analysis(tcx, owner_fn_id),
    }
}

fn model_assuming_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    model_ty: DefId,
) -> mir_ty::TypingEnv<'tcx> {
    use mir_ty::Upcast as _;
    let env = mir_ty::TypingEnv::post_analysis(tcx, caller_def_id);
    let model_trait = tcx.parent(model_ty);
    let Some(eq_trait) = tcx.lang_items().eq_trait() else {
        return env;
    };
    let generics = tcx.generics_of(caller_def_id);
    let assumed = (0..generics.count())
        .map(|idx| generics.param_at(idx, tcx))
        .filter(|param| matches!(param.kind, mir_ty::GenericParamDefKind::Type { .. }))
        .map(|param| tcx.mk_param_from_def(param).expect_ty())
        .flat_map(|ty| {
            let model = mir_ty::Ty::new_projection(tcx, model_ty, [ty]);
            [
                mir_ty::TraitRef::new(tcx, model_trait, [ty]).upcast(tcx),
                mir_ty::TraitRef::new(tcx, eq_trait, [model, model]).upcast(tcx),
            ]
        });
    let clauses = tcx.mk_clauses_from_iter(env.param_env.caller_bounds().iter().chain(assumed));
    mir_ty::TypingEnv {
        param_env: mir_ty::ParamEnv::new(clauses),
        ..env
    }
}

fn match_spec_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    spec_arg: mir_ty::GenericArg<'tcx>,
    actual_arg: mir_ty::GenericArg<'tcx>,
    bound: &mut HashMap<u32, mir_ty::GenericArg<'tcx>>,
) -> bool {
    use mir_ty::GenericArgKind as K;
    match (spec_arg.kind(), actual_arg.kind()) {
        (K::Lifetime(_), K::Lifetime(_)) => true,
        (K::Type(spec_ty), K::Type(actual_ty)) => match_spec_ty(tcx, spec_ty, actual_ty, bound),
        (K::Const(spec_ct), K::Const(actual_ct)) => match spec_ct.kind() {
            mir_ty::ConstKind::Param(p) => bind_spec_param(tcx, p.index, actual_arg, bound),
            _ => spec_ct == actual_ct,
        },
        _ => false,
    }
}

fn match_spec_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    spec_ty: mir_ty::Ty<'tcx>,
    actual_ty: mir_ty::Ty<'tcx>,
    bound: &mut HashMap<u32, mir_ty::GenericArg<'tcx>>,
) -> bool {
    use mir_ty::TyKind as T;
    use mir_ty::TypeVisitableExt as _;
    match (spec_ty.kind(), actual_ty.kind()) {
        (T::Param(p), _) => bind_spec_param(tcx, p.index, actual_ty.into(), bound),
        (T::Adt(spec_def, spec_args), T::Adt(actual_def, actual_args)) => {
            spec_def == actual_def
                && spec_args
                    .iter()
                    .zip(actual_args.iter())
                    .all(|(s, a)| match_spec_arg(tcx, s, a, bound))
        }
        (T::Array(spec_elem, spec_len), T::Array(actual_elem, actual_len)) => {
            match_spec_ty(tcx, *spec_elem, *actual_elem, bound)
                && match_spec_arg(tcx, (*spec_len).into(), (*actual_len).into(), bound)
        }
        (T::Slice(spec_elem), T::Slice(actual_elem)) => {
            match_spec_ty(tcx, *spec_elem, *actual_elem, bound)
        }
        (T::Ref(_, spec_inner, spec_mut), T::Ref(_, actual_inner, actual_mut)) => {
            spec_mut == actual_mut && match_spec_ty(tcx, *spec_inner, *actual_inner, bound)
        }
        (T::Tuple(spec_tys), T::Tuple(actual_tys)) => {
            spec_tys.len() == actual_tys.len()
                && spec_tys
                    .iter()
                    .zip(actual_tys.iter())
                    .all(|(s, a)| match_spec_ty(tcx, s, a, bound))
        }
        _ => !spec_ty.has_param() && tcx.erase_regions(spec_ty) == tcx.erase_regions(actual_ty),
    }
}

fn bind_spec_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    index: u32,
    actual_arg: mir_ty::GenericArg<'tcx>,
    bound: &mut HashMap<u32, mir_ty::GenericArg<'tcx>>,
) -> bool {
    let actual_arg = tcx.erase_regions(actual_arg);
    *bound.entry(index).or_insert(actual_arg) == actual_arg
}

#[derive(Debug, Clone)]
struct GenericDefTy<'tcx> {
    // this is different from a key in defs when the def is extern_spec_fn
    local_def_id: LocalDefId,
    cache: Rc<RefCell<HashMap<InstantiationKey<'tcx>, rty::RefinedType>>>,
    rty: Option<rty::RefinedType>,
}

// TODO: key this on the callee and its arguments alone, once analyzing a body no longer
// depends on who is calling.
//
// `caller_def_id` is here because the body of a generic def is re-analyzed under the
// caller's `owner_fn_id`, and that owner is what interprets a `ParamTy`'s index: without
// it, `TypeBuilder::param_def_id` resolves index 0 of one def and index 0 of another to
// the same declaration site. It also selects the `TypingEnv` normalization runs in and
// mints the closure pre/post forall-pred identities. So a body is analyzed once per
// (type arguments, calling function) rather than once per monomorphization, which is
// superlinear in call sites -- the shape that a small generic function called from many
// places runs into. Giving the body analysis the callee as its owner would make it
// caller-independent and let this be a monomorphization cache.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct InstantiationKey<'tcx> {
    generic_args: mir_ty::GenericArgsRef<'tcx>,
    caller_def_id: DefId,
}

/// Identifies one instance of a predicate with a Rust body: the predicate, its generic
/// arguments, and the calling function when those arguments mention its type parameters.
type PredicateInstanceKey<'tcx> = (DefId, mir_ty::GenericArgsRef<'tcx>, Option<DefId>);

/// Identifies one analysis instance of a function body.
///
/// A def may be analyzed more than once: the placeholder analysis (with the
/// type parameters left as forall sorts) and, when a generic def is called at
/// concrete type arguments, one analysis per instantiation. Each instance owns
/// its own basic-block types so that nested analyses of the same def (e.g. a
/// recursive generic function) do not clobber each other.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct AnalysisKey<'tcx> {
    local_def_id: LocalDefId,
    generic_args: mir_ty::GenericArgsRef<'tcx>,
    owner_fn_id: DefId,
}

impl<'tcx> AnalysisKey<'tcx> {
    pub fn new(
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Self {
        Self {
            local_def_id,
            generic_args,
            owner_fn_id,
        }
    }

    /// The typing environment for resolving associated types, layouts and instances in the
    /// analyzed body. When the body is instantiated at a caller's generic arguments that still
    /// mention the caller's type parameters, only the caller's (`owner_fn_id`'s) where-clauses
    /// can resolve a projection over them, so its environment is used; otherwise the body's own.
    pub fn typing_env(&self, tcx: TyCtxt<'tcx>) -> mir_ty::TypingEnv<'tcx> {
        use mir_ty::TypeVisitableExt as _;
        let identity = mir_ty::GenericArgs::identity_for_item(tcx, self.local_def_id);
        if self.generic_args.has_param() && self.generic_args != identity {
            mir_ty::TypingEnv::post_analysis(tcx, self.owner_fn_id)
        } else {
            mir_ty::TypingEnv::post_analysis(tcx, self.local_def_id)
        }
    }
}

#[derive(Debug, Clone)]
enum DefTy<'tcx> {
    Concrete(rty::RefinedType),
    Generic(GenericDefTy<'tcx>),
    // Several extern specs can share one target, each covering the instantiations its tail call
    // and bounds cover (see `bind_spec_args`); a call takes the first one that covers it.
    Deferred(Vec<DeferredDefTy<'tcx>>),
}

#[derive(Debug, Clone)]
struct BasicBlockDef {
    ty: BasicBlockType,
    has_precondition: bool,
    has_param_types: bool,
}

#[derive(Debug, Clone, Default)]
pub struct EnumDefs {
    defs: HashMap<DefId, rty::EnumDatatypeDef>,
}

impl EnumDefs {
    pub fn find_by_name(&self, name: &chc::DatatypeSymbol) -> Option<&rty::EnumDatatypeDef> {
        self.defs.values().find(|def| &def.name == name)
    }

    pub fn get(&self, def_id: DefId) -> Option<&rty::EnumDatatypeDef> {
        self.defs.get(&def_id)
    }

    pub fn insert(&mut self, def_id: DefId, def: rty::EnumDatatypeDef) {
        self.defs.insert(def_id, def);
    }
}

impl refine::EnumDefProvider for Rc<RefCell<EnumDefs>> {
    fn enum_def(&self, name: &chc::DatatypeSymbol) -> rty::EnumDatatypeDef {
        self.borrow().find_by_name(name).unwrap().clone()
    }
}

pub type Env = refine::Env<Rc<RefCell<EnumDefs>>>;
pub type TypeParamMap<'tcx> = HashMap<TypeParam, ForallSortIdx>;

#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum TypeParam {
    /// A type parameter identified by its declaration def_id and its
    /// **local** index within the declaring item (i.e. lifetime and const
    /// parameters are skipped). Using the local index lets monomorphization
    /// substitute it with the actual generic argument at the same position.
    GenericType {
        param_def_id: DefId,
        local_idx: u32,
    },
    AssocType(DefId, Vec<rty::Type<rty::Closed>>),
}

#[derive(Debug, Clone)]
struct DeferredFormulaFnDef<'tcx> {
    // Keyed on the owner as well as the type arguments: a lifted formula is translated
    // under the owner's `TypeBuilder`, which is what turns a `ParamTy` into a forall sort.
    // Two functions each declaring a first type parameter are indistinguishable by their
    // `GenericArgsRef` alone, so dropping the owner hands one function's translation --
    // its forall sorts, and the trait predicate instances named after them -- to the other.
    cache: Rc<RefCell<HashMap<InstantiationKey<'tcx>, annot_fn::FormulaFn<'tcx>>>>,
}

#[derive(Clone)]
pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,

    /// Collection of refined known def types.
    ///
    /// currently contains only local-def templates,
    /// but will be extended to contain externally known def's refinement types
    /// (at least for every defs referenced by local def bodies)
    defs: HashMap<DefId, DefTy<'tcx>>,

    /// Collection of functions with `#[thrust::formula_fn]` attribute.
    formula_fns: HashMap<LocalDefId, DeferredFormulaFnDef<'tcx>>,
    /// Instances of predicates with a Rust body; see [`Analyzer::predicate_with_args`].
    predicate_instances: Rc<RefCell<HashMap<PredicateInstanceKey<'tcx>, chc::UserDefinedPred>>>,

    /// Resulting CHC system.
    system: Rc<RefCell<chc::System>>,

    basic_blocks: HashMap<AnalysisKey<'tcx>, HashMap<BasicBlock, BasicBlockDef>>,
    def_ids: did_cache::DefIdCache<'tcx>,

    enum_defs: Rc<RefCell<EnumDefs>>,

    type_params: Rc<RefCell<TypeParamMap<'tcx>>>,
    closure_type_params: Rc<RefCell<HashMap<TypeParam, rty::FunctionType>>>,

    /// Where each [`chc::ForallPred`] standing for a trait predicate came from,
    /// so that an instantiation of the item that quantified over it can say
    /// which impl's predicate it resolves to.
    forall_pred_origins: Rc<RefCell<HashMap<chc::ForallPred, pred_inst::ForallPredOrigin<'tcx>>>>,
    /// Predicate definitions an instantiation asked for and that
    /// [`Analyzer::emit_pending_pred_instances`] has yet to emit.
    pending_pred_instances: Rc<RefCell<Vec<pred_inst::PendingPredInstance<'tcx>>>>,
    /// The `#[thrust::law]` functions of each trait, keyed by the trait, in the order the traits'
    /// laws were registered (source order), so that the laws are checked in the same order on
    /// every run: the order decides the numbering of the unknowns and the order of the clauses,
    /// which the solver's time depends on (see `analyze_local_defs`).
    trait_laws: Rc<RefCell<rustc_data_structures::fx::FxIndexMap<DefId, Vec<DefId>>>>,
    /// Uses of a trait predicate through a type parameter whose laws
    /// [`Analyzer::emit_pending_laws`] has yet to state.
    pending_laws: Rc<RefCell<Vec<pred_inst::PendingLaw<'tcx>>>>,
    /// Defs whose body has been analyzed at fully concrete type arguments, as the callee of
    /// a call site; see [`Analyzer::has_concrete_instance`].
    concrete_instances: Rc<RefCell<HashSet<LocalDefId>>>,
    /// The closure types, generic arguments included, with the sort of their upvars, whose
    /// `hist_inv` clause has had its laws pushed; see [`closure_hist_inv::explicit_laws`].
    explicit_hist_inv_laws: Rc<RefCell<HashSet<(mir_ty::Ty<'tcx>, chc::Sort)>>>,
    /// The unknown relating the by-value captures of an `FnMut` closure whose specification has
    /// no `hist_inv` clause, one per closure type and upvars sort; see
    /// [`Analyzer::closure_hist_inv_definition`].
    by_value_hist_invs: Rc<RefCell<HashMap<(mir_ty::Ty<'tcx>, chc::Sort), chc::PredVarId>>>,
    /// The clauses [`closure_hist_inv::instance_obligations`] gave for the instances at an `FnMut`
    /// closure that use a generic def's contract as instantiated: the `hist_inv!` laws and the
    /// precondition clauses, pushed by [`Analyzer::emit_fn_mut_instance_obligations`].
    fn_mut_instance_obligations: Rc<RefCell<FnMutInstanceObligations>>,
    /// See [`Analyzer::record_hist_inv_specified_params`].
    hist_inv_specified_params: Rc<RefCell<HashSet<DefId>>>,
    /// The local fn-like defs with an `FnMut`-bounded type parameter, recorded with
    /// [`Analyzer::hist_inv_specified_params`].
    fn_mut_bounded_defs: Rc<RefCell<Vec<DefId>>>,
    /// The spec bounds a body assumed at a type parameter or an unresolved projection, keyed by
    /// the typeck root of the def it was analysed under; see [`classify_spec_bounds`].
    assumed_spec_bounds: RefCell<HashMap<DefId, Vec<mir_ty::Clause<'tcx>>>>,
    /// The instances `(def, generic args, caller)` that use a generic def's contract as
    /// instantiated; see [`Analyzer::check_reused_spec_bounds`].
    reused_generic_instances: RefCell<Vec<(DefId, mir_ty::GenericArgsRef<'tcx>, DefId)>>,
    /// The trait methods without a specification a body called at its type parameters, keyed
    /// like `assumed_spec_bounds`; see [`Analyzer::check_reused_total_methods`].
    assumed_total_methods: RefCell<HashMap<DefId, Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)>>>,
    /// The types of the functions each basic block calls, recorded only when
    /// [`candidate_atoms_enabled`], whose contracts give a loop head candidate atoms.
    called_fn_tys: HashMap<(AnalysisKey<'tcx>, BasicBlock), Vec<rty::FunctionType>>,
}

/// Whether loop heads get candidate atoms (`THRUST_CANDIDATE_ATOMS`, see
/// [`chc::CandidateAtomsMode`]).
pub fn candidate_atoms_enabled() -> bool {
    chc::CandidateAtomsMode::from_env() != chc::CandidateAtomsMode::Off
}

impl<'tcx> crate::refine::TemplateRegistry for Analyzer<'tcx> {
    fn register_template<V>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V> {
        tmpl.into_refined_type(|pred_sig| self.generate_pred_var(pred_sig))
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn generate_pred_var(&mut self, sig: chc::PredSig) -> chc::PredVarId {
        self.system
            .borrow_mut()
            .new_pred_var(sig, chc::DebugInfo::from_current_span())
    }

    pub fn generate_user_quantified_var(&self, name: String) -> chc::UserQuantifiedVarId {
        self.system.borrow_mut().new_named_user_quantified_var(name)
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let defs = Default::default();
        let formula_fns = Default::default();
        let system = Default::default();
        let basic_blocks = Default::default();
        let enum_defs = Default::default();
        let type_params = Default::default();
        let closure_type_params = Default::default();
        let forall_pred_origins = Default::default();
        let pending_pred_instances = Default::default();
        let trait_laws = Default::default();
        let pending_laws = Default::default();
        Self {
            tcx,
            defs,
            formula_fns,
            predicate_instances: Default::default(),
            system,
            basic_blocks,
            def_ids: did_cache::DefIdCache::new(tcx),
            enum_defs,
            type_params,
            closure_type_params,
            forall_pred_origins,
            pending_pred_instances,
            trait_laws,
            pending_laws,
            concrete_instances: Default::default(),
            explicit_hist_inv_laws: Default::default(),
            by_value_hist_invs: Default::default(),
            fn_mut_instance_obligations: Default::default(),
            hist_inv_specified_params: Default::default(),
            fn_mut_bounded_defs: Default::default(),
            assumed_spec_bounds: Default::default(),
            reused_generic_instances: Default::default(),
            assumed_total_methods: Default::default(),
            called_fn_tys: Default::default(),
        }
    }

    pub fn def_ids(&self) -> did_cache::DefIdCache<'tcx> {
        // DefIdCache is backed by Rc
        self.def_ids.clone()
    }

    pub fn record_called_fn_ty(
        &mut self,
        key: AnalysisKey<'tcx>,
        bb: BasicBlock,
        fn_ty: rty::FunctionType,
    ) {
        self.called_fn_tys.entry((key, bb)).or_default().push(fn_ty);
    }

    pub fn called_fn_tys(&self, key: AnalysisKey<'tcx>, bb: BasicBlock) -> &[rty::FunctionType] {
        self.called_fn_tys
            .get(&(key, bb))
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn pred_var_sig(&self, pred: chc::PredVarId) -> chc::PredSig {
        self.system.borrow().pred_vars[pred].sig.clone()
    }

    pub fn push_candidate_atoms(&mut self, pred: chc::PredVarId, atoms: Vec<chc::Formula>) {
        self.system.borrow_mut().push_candidate_atoms(pred, atoms);
    }

    pub fn add_clause(&mut self, clause: chc::Clause) {
        self.system.borrow_mut().push_clause(clause);
    }

    pub fn extend_clauses(&mut self, clauses: impl IntoIterator<Item = chc::Clause>) {
        for clause in clauses {
            self.add_clause(clause);
        }
    }

    fn build_enum_def(&self, def_id: DefId) -> rty::EnumDatatypeDef {
        let adt = self.tcx.adt_def(def_id);

        let name = refine::datatype_symbol(self.tcx, def_id);
        let variants: IndexVec<_, _> = adt
            .variants()
            .iter()
            .zip(adt.discriminants(self.tcx))
            .map(|(variant, (_, discr))| {
                let discr = discr_value(self.tcx, discr);
                let field_tys = variant
                    .fields
                    .iter()
                    .map(|field| {
                        let field_ty = self.tcx.type_of(field.did).instantiate_identity();
                        self.type_builder(self.def_ids(), def_id).build(field_ty)
                    })
                    .collect();
                rty::EnumVariantDef {
                    name: chc::DatatypeSymbol::new(format!("{}.{}", name, variant.name)),
                    discr,
                    field_tys,
                }
            })
            .collect();

        let generics = self.tcx.generics_of(def_id);
        let ty_params = (0..generics.count())
            .filter(|idx| {
                matches!(
                    generics.param_at(*idx, self.tcx).kind,
                    mir_ty::GenericParamDefKind::Type { .. }
                )
            })
            .count();
        tracing::debug!(?def_id, ?name, ?ty_params, "ty_params count");

        rty::EnumDatatypeDef {
            name,
            ty_params,
            variants,
        }
    }

    pub fn get_or_register_enum_def(&self, def_id: DefId) -> rty::EnumDatatypeDef {
        let mut enum_defs = self.enum_defs.borrow_mut();
        if let Some(enum_def) = enum_defs.get(def_id) {
            return enum_def.clone();
        }

        let enum_def = self.build_enum_def(def_id);
        tracing::debug!(def_id = ?def_id, enum_def = ?enum_def, "register_enum_def");
        let ctors = enum_def
            .variants
            .iter()
            .map(|v| chc::DatatypeCtor {
                symbol: v.name.clone(),
                selectors: v
                    .field_tys
                    .clone()
                    .into_iter()
                    .enumerate()
                    .map(|(idx, ty)| chc::DatatypeSelector {
                        symbol: chc::DatatypeSymbol::new(format!("_get{}.{}", v.name, idx)),
                        sort: ty.to_sort(),
                    })
                    .collect(),
                discriminant: v.discr.clone(),
            })
            .collect();
        let datatype = chc::Datatype {
            symbol: enum_def.name.clone(),
            params: enum_def.ty_params,
            ctors,
        };
        enum_defs.insert(def_id, enum_def.clone());
        self.system.borrow_mut().datatypes.push(datatype);

        enum_def
    }

    /// Registers the enums that occur in `tys`, in the order they are visited: that order reaches
    /// the emitted datatype declarations.
    pub fn register_enum_defs(
        &self,
        tys: impl IntoIterator<Item = mir_ty::Ty<'tcx>>,
        builder: TypeBuilder<'tcx>,
    ) {
        use mir_ty::{TypeSuperVisitable as _, TypeVisitable as _};
        struct EnumCollector<'tcx> {
            tcx: TyCtxt<'tcx>,
            builder: TypeBuilder<'tcx>,
            enums: rustc_data_structures::fx::FxIndexSet<DefId>,
            visited: HashSet<mir_ty::Ty<'tcx>>,
        }
        impl<'tcx> mir_ty::TypeVisitor<TyCtxt<'tcx>> for EnumCollector<'tcx> {
            fn visit_ty(&mut self, ty: mir_ty::Ty<'tcx>) {
                let ty = self.builder.resolve_model_ty(ty);
                // Each type once: the const argument of a model such as `UIntN<64>` has type
                // `usize`, whose model is that type again.
                if !self.visited.insert(ty) {
                    return;
                }
                if let mir_ty::TyKind::Adt(def, args) = ty.kind() {
                    if def.is_enum() {
                        self.enums.insert(def.did());
                    }
                    for field in def.all_fields() {
                        field.ty(self.tcx, args).visit_with(self);
                    }
                }
                ty.super_visit_with(self);
            }
        }
        let mut visitor = EnumCollector {
            tcx: self.tcx,
            builder,
            enums: Default::default(),
            visited: HashSet::new(),
        };
        for ty in tys {
            ty.visit_with(&mut visitor);
        }
        for def_id in visitor.enums {
            self.get_or_register_enum_def(def_id);
        }
    }

    pub fn register_def(&mut self, def_id: DefId, rty: rty::RefinedType) {
        tracing::info!(def_id = ?def_id, rty = %rty.display(), "register_def");
        self.defs.insert(def_id, DefTy::Concrete(rty));
    }

    pub fn register_deferred_def(
        &mut self,
        target_def_id: DefId,
        local_def_id: LocalDefId,
        target_args: Option<mir_ty::GenericArgsRef<'tcx>>,
    ) {
        self.register_deferred_def_impl(
            target_def_id,
            local_def_id,
            target_args,
            DeferredDefMode::Analyze,
        );
    }

    pub fn register_deferred_def_without_analysis(
        &mut self,
        target_def_id: DefId,
        local_def_id: LocalDefId,
        target_args: Option<mir_ty::GenericArgsRef<'tcx>>,
    ) {
        self.register_deferred_def_impl(
            target_def_id,
            local_def_id,
            target_args,
            DeferredDefMode::NoAnalyze,
        );
    }

    fn register_deferred_def_impl(
        &mut self,
        target_def_id: DefId,
        local_def_id: LocalDefId,
        target_args: Option<mir_ty::GenericArgsRef<'tcx>>,
        mode: DeferredDefMode,
    ) {
        tracing::info!(
            ?target_def_id,
            ?local_def_id,
            ?target_args,
            ?mode,
            "register_deferred_def"
        );
        let spec = DeferredDefTy {
            local_def_id,
            cache: Rc::new(RefCell::new(HashMap::new())),
            mode,
            target_args,
        };
        if let DefTy::Deferred(specs) = self
            .defs
            .entry(target_def_id)
            .or_insert_with(|| DefTy::Deferred(Vec::new()))
        {
            specs.push(spec);
        }
    }

    pub fn register_generic_def(
        &mut self,
        target_def_id: DefId,
        local_def_id: LocalDefId,
        rty: Option<rty::RefinedType>,
    ) {
        tracing::info!(?target_def_id, ?local_def_id, ?rty, "register_generic_def");
        self.defs.insert(
            target_def_id,
            DefTy::Generic(GenericDefTy {
                rty,
                local_def_id,
                cache: Rc::new(RefCell::new(HashMap::new())),
            }),
        );
    }

    pub fn get_closure_type(&self, type_param: TypeParam) -> Option<rty::FunctionType> {
        self.closure_type_params.borrow().get(&type_param).cloned()
    }

    pub fn concrete_def_ty(&self, def_id: DefId) -> Option<&rty::RefinedType> {
        self.defs.get(&def_id).and_then(|def_ty| match def_ty {
            DefTy::Concrete(rty) => Some(rty),
            DefTy::Generic(GenericDefTy { rty, .. }) => rty.as_ref(),
            DefTy::Deferred(_) => None,
        })
    }

    // TODO: Remove this cache-only accessor together with
    // `local_def::Analyzer::precompute_callable_param_contracts` once `def_ty_with_args` can be
    // used from formula translation without requiring `&mut Analyzer`.
    pub fn known_function_ty_with_args(
        &self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> Option<rty::FunctionType> {
        let type_builder = TypeBuilder::new(
            self.tcx,
            self.def_ids(),
            def_id,
            self.type_params.clone(),
            self.closure_type_params.clone(),
            self.system.clone(),
        );
        let key = InstantiationKey {
            generic_args,
            caller_def_id,
        };
        let mut def_ty = match self.defs.get(&def_id)? {
            DefTy::Concrete(rty) => rty.clone(),
            DefTy::Generic(generic) => generic.cache.borrow().get(&key)?.clone(),
            DefTy::Deferred(specs) => specs
                .iter()
                .find_map(|spec| spec.cache.borrow().get(&key).cloned())?,
        };
        def_ty.instantiate_ty_params(
            generic_args
                .types()
                .map(|ty| type_builder.build(ty))
                .collect(),
        );
        def_ty.ty.as_function().cloned()
    }

    /// The predicate symbol for a call to the predicate `def_id` at `generic_args`, made from
    /// `owner_fn_id`. A logic function is instantiated the same way.
    ///
    /// A predicate with a Rust body is defined once per instantiation. When the arguments still
    /// mention type parameters, those belong to `owner_fn_id` and translate to its forall sorts,
    /// so the instance is keyed by the owner as well.
    pub fn predicate_with_args(
        &self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> chc::UserDefinedPred {
        let Some(local_def_id) = def_id
            .as_local()
            .filter(|id| self.formula_fns.contains_key(id))
        else {
            return self.user_defined_pred_at_args(def_id, generic_args, owner_fn_id);
        };
        use mir_ty::TypeVisitableExt as _;
        let key = (
            def_id,
            generic_args,
            generic_args.has_param().then_some(owner_fn_id),
        );
        if let Some(pred) = self.predicate_instances.borrow().get(&key) {
            return pred.clone();
        }
        let pred = chc::UserDefinedPred::new(format!(
            "{}_{}",
            refine::user_defined_pred(self.tcx, def_id),
            self.predicate_instances.borrow().len(),
        ));
        self.predicate_instances
            .borrow_mut()
            .insert(key, pred.clone());

        let formula_fn = self
            .formula_fn_with_args(local_def_id, generic_args, owner_fn_id)
            .unwrap();
        let type_builder = self.type_builder(self.def_ids(), owner_fn_id);
        self.register_enum_defs(
            formula_fn
                .params()
                .iter()
                .copied()
                .chain(std::iter::once(formula_fn.ret())),
            type_builder.clone(),
        );
        let arg_sorts = formula_fn
            .params()
            .iter()
            .map(|ty| type_builder.build(*ty).to_sort())
            .collect();
        let mut system = self.system.borrow_mut();
        match formula_fn.body() {
            annot_fn::FormulaFnBody::Formula(formula) => system.push_pred_define_formula(
                pred.clone(),
                arg_sorts,
                formula
                    .clone()
                    .map_var(|idx| chc::TermVarIdx::from(idx.index())),
            ),
            annot_fn::FormulaFnBody::Term(term) => system.push_fn_define_term(
                pred.clone(),
                arg_sorts,
                type_builder.build(formula_fn.ret()).to_sort(),
                term.clone()
                    .map_var(|idx| chc::TermVarIdx::from(idx.index())),
            ),
        }
        pred
    }

    /// The symbol and result sort for a call to the `#[thrust_macros::logic]` function `def_id`
    /// at `generic_args`, defined like a predicate instance.
    pub fn logic_fn_with_args(
        &self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> (chc::UserDefinedPred, chc::Sort) {
        let symbol = self.predicate_with_args(def_id, generic_args, owner_fn_id);
        let ret = self
            .formula_fn_with_args(def_id.expect_local(), generic_args, owner_fn_id)
            .expect("a logic function has a Rust body")
            .ret();
        let ret_sort = self
            .type_builder(self.def_ids(), owner_fn_id)
            .build(ret)
            .to_sort();
        (symbol, ret_sort)
    }

    pub fn formula_fn_with_args(
        &self,
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<annot_fn::FormulaFn<'tcx>> {
        let deferred_formula_fn = self.formula_fns.get(&local_def_id)?;

        let key = InstantiationKey {
            generic_args,
            caller_def_id: owner_fn_id,
        };
        let deferred_formula_fn_cache = Rc::clone(&deferred_formula_fn.cache);
        if let Some(formula_fn) = deferred_formula_fn_cache.borrow().get(&key) {
            return Some(formula_fn.clone());
        }

        let translator =
            annot_fn::AnnotFnTranslator::new(self, local_def_id, generic_args, owner_fn_id)
                .with_def_id_cache(self.def_ids());
        let formula_fn = translator.to_formula_fn();
        deferred_formula_fn_cache
            .borrow_mut()
            .insert(key, formula_fn.clone());

        tracing::info!(?local_def_id, formula_fn = %formula_fn.display(), ?generic_args, "formula_fn_with_args");
        Some(formula_fn)
    }

    fn instantiate_generic_args(
        ty: &mut rty::RefinedType,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        type_builder: &TypeBuilder<'tcx>,
    ) {
        ty.instantiate_ty_params(
            generic_args
                .types()
                .map(|ty| type_builder.build(ty))
                .collect(),
        );
    }

    /// The generic arguments of `spec` at a call of its target at `generic_args`, or `None` when
    /// the spec does not cover the call.
    ///
    /// A def_id key can be a blanket impl shared by more instantiations than an extern spec's own
    /// tail call covers (e.g. `Vec::index` at some `Idx` other than the `usize`
    /// `_extern_spec_vec_index` calls it at). Handing such a call that spec's contract would relate
    /// its result to whatever the spec's own body happens to return, regardless of the real `Idx`
    /// here.
    fn spec_args(
        &self,
        spec: &DeferredDefTy<'tcx>,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> Option<mir_ty::GenericArgsRef<'tcx>> {
        let Some(target_args) = spec.target_args else {
            return Some(generic_args);
        };
        let bound = bind_spec_args(self.tcx, spec.local_def_id, target_args, generic_args)?;
        let Some(model_ty) = self.def_ids().model_ty() else {
            return Some(bound);
        };
        let model_trait = self.tcx.parent(model_ty);
        let clauses = self
            .tcx
            .predicates_of(spec.local_def_id)
            .instantiate(self.tcx, bound)
            .predicates
            .into_iter()
            .filter(|clause| is_spec_bound(*clause, model_trait));
        let assumed = classify_spec_bounds(self.tcx, clauses, caller_def_id, model_ty).ok()?;
        self.record_assumed_spec_bounds(caller_def_id, assumed);
        Some(bound)
    }

    /// Records spec bounds assumed while analysing a body owned by `owner_fn_id`, under its typeck
    /// root: a closure's body is verified as part of the fn it is in. Returns whether any is new.
    fn record_assumed_spec_bounds(
        &self,
        owner_fn_id: DefId,
        clauses: Vec<mir_ty::Clause<'tcx>>,
    ) -> bool {
        let root = self.tcx.typeck_root_def_id(owner_fn_id);
        let mut assumed = self.assumed_spec_bounds.borrow_mut();
        let recorded = assumed.entry(root).or_default();
        let mut grew = false;
        for clause in clauses {
            let clause = self.tcx.erase_regions(clause);
            if !recorded.contains(&clause) {
                recorded.push(clause);
                grew = true;
            }
        }
        grew
    }

    /// Checks the spec bounds each generic def's analysis assumed at its type parameters
    /// ([`classify_spec_bounds`]) at every instance that uses its contract as instantiated.
    ///
    /// Creusot requires such a bound (`T::IntoIter: IteratorSpec` of `FromIterator::from_iter`'s
    /// extern spec) to be provable at each call, so a generic caller must declare it and rustc
    /// checks it at the caller's instantiations. Here the bound is assumed at the caller's type
    /// parameters instead, so this checks it at each instance, after every body is analysed, when
    /// all the assumptions are known. A bound still at a type parameter of the instance's caller
    /// is assumed by that caller in turn, until nothing new is assumed. A program with an instance
    /// at which a bound fails is rejected: the generic contract does not stand for it, and its
    /// body would call a spec that does not cover it, as a direct call there does.
    pub fn check_reused_spec_bounds(&self) {
        let Some(model_ty) = self.def_ids().model_ty() else {
            return;
        };
        loop {
            let mut grew = false;
            for &(def_id, generic_args, caller_def_id) in
                self.reused_generic_instances.borrow().iter()
            {
                let root = self.tcx.typeck_root_def_id(def_id);
                let assumed = self
                    .assumed_spec_bounds
                    .borrow()
                    .get(&root)
                    .cloned()
                    .unwrap_or_default();
                let clauses = assumed.into_iter().map(|clause| {
                    mir_ty::EarlyBinder::bind(clause).instantiate(self.tcx, generic_args)
                });
                match classify_spec_bounds(self.tcx, clauses, caller_def_id, model_ty) {
                    Ok(assumed) => grew |= self.record_assumed_spec_bounds(caller_def_id, assumed),
                    Err(clause) => self.tcx.dcx().fatal(format!(
                        "spec bound not satisfied: `{}` is verified generically under a spec \
                         bound at its type parameters, which does not hold at its instance \
                         `{}` used in `{}`: `{clause}`",
                        self.tcx.def_path_str(def_id),
                        self.tcx.def_path_str_with_args(def_id, generic_args),
                        self.tcx.def_path_str(caller_def_id),
                    )),
                }
            }
            if !grew {
                return;
            }
        }
    }

    /// Records that a body analysed under `owner_fn_id` called the trait method `def_id`, which
    /// has no specification, at `generic_args` that name type parameters, and so took it to
    /// accept any arguments. Returns whether it is new.
    pub fn record_assumed_total_method(
        &self,
        owner_fn_id: DefId,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> bool {
        let root = self.tcx.typeck_root_def_id(owner_fn_id);
        let call = (def_id, self.tcx.erase_regions(generic_args));
        let mut assumed = self.assumed_total_methods.borrow_mut();
        let recorded = assumed.entry(root).or_default();
        if recorded.contains(&call) {
            return false;
        }
        recorded.push(call);
        true
    }

    /// Checks, at each instance that uses a generic def's contract as instantiated, that every
    /// trait method its analysis called without a specification at a type parameter
    /// ([`Self::record_assumed_total_method`]) accepts any arguments there: the precondition of
    /// the impl the call resolves to holds of all of them. A call still at a type parameter of
    /// the instance's caller is assumed by that caller in turn, as
    /// [`Self::check_reused_spec_bounds`] does with spec bounds. An impl Thrust knows no contract
    /// of is not checked, as a direct call to it cannot be analysed either.
    pub fn check_reused_total_methods(&mut self) {
        use mir_ty::TypeVisitableExt as _;

        let mut checked = HashSet::new();
        let mut seen_instances = 0;
        loop {
            let instances = self.reused_generic_instances.borrow().clone();
            let mut grew = instances.len() != seen_instances;
            seen_instances = instances.len();
            for (def_id, generic_args, caller_def_id) in instances {
                let root = self.tcx.typeck_root_def_id(def_id);
                let assumed = self
                    .assumed_total_methods
                    .borrow()
                    .get(&root)
                    .cloned()
                    .unwrap_or_default();
                for (method, method_args) in assumed {
                    let method_args =
                        mir_ty::EarlyBinder::bind(method_args).instantiate(self.tcx, generic_args);
                    if method_args.has_param() {
                        grew |=
                            self.record_assumed_total_method(caller_def_id, method, method_args);
                    } else if checked.insert((method, method_args)) {
                        self.check_total_method(method, method_args, caller_def_id);
                    }
                }
            }
            if !grew {
                return;
            }
        }
    }

    fn check_total_method(
        &mut self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let Ok(Some(instance)) =
            mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, generic_args)
        else {
            return;
        };
        let Some(def_ty) = self.def_ty_with_args(instance.def_id(), instance.args, caller_def_id)
        else {
            return;
        };
        let fn_ty = def_ty
            .ty
            .as_function()
            .expect("a method has a function type");
        let mut builder = chc::ClauseBuilder::default();
        let args: IndexVec<rty::FunctionParamIdx, _> = fn_ty
            .params
            .iter()
            .map(|param| chc::Term::var(builder.add_var(param.ty.to_sort())))
            .collect();
        let mut pre = chc::Body::top();
        for (idx, param) in fn_ty.params.iter_enumerated() {
            assert!(param.refinement.existentials.is_empty());
            pre.push_conj(param.refinement.body.clone().subst_var(|v| match v {
                rty::RefinedTypeVar::Value => args[idx].clone(),
                rty::RefinedTypeVar::Free(j) => args[j].clone(),
                rty::RefinedTypeVar::Existential(_) => unreachable!(),
            }));
        }
        let origin = chc::debug::origin::Entry::described(format!(
            "precondition of {instance} at any arguments, assumed by a generic analysis"
        ));
        let clauses = builder.head(pre, origin);
        self.extend_clauses(clauses);
    }

    pub fn def_ty_with_args(
        &mut self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> Option<rty::RefinedType> {
        let type_builder = self.type_builder(self.def_ids(), caller_def_id);

        let is_generic = matches!(self.defs.get(&def_id)?, DefTy::Generic(_));
        let (local_def_id, instantiated_ty_cache, deferred_ty_mode, generic_args) =
            match self.defs.get(&def_id)? {
                DefTy::Concrete(rty) => {
                    let mut def_ty = rty.clone();
                    Self::instantiate_generic_args(&mut def_ty, generic_args, &type_builder);
                    return Some(def_ty);
                }
                DefTy::Generic(generic) => (
                    generic.local_def_id,
                    Rc::clone(&generic.cache),
                    Some(DeferredDefMode::Analyze).filter(|_| {
                        use mir_ty::TypeVisitableExt as _;
                        if !generic_args.types().any(|ty| ty.has_param()) {
                            return true;
                        }
                        // The type arguments are the caller's own type parameters, so
                        // the contract minted just below lives on the caller's abstract
                        // sorts while the placeholder analysis constrains one on the
                        // callee's. Analyzing the body here, under the caller as its
                        // owner, is what puts a defining clause under that contract;
                        // without it the contract is free and the caller is vacuous
                        // from this call onwards.
                        //
                        // Two shapes are kept out:
                        // - a call that lands back on the def whose analysis we are
                        //   inside, which would re-enter that same analysis instance;
                        // - a def whose contract comes from a separate spec function,
                        //   whose body is analyzed under its own owner and so would be
                        //   typed over sorts the call site does not share.
                        def_id != caller_def_id && generic.local_def_id.to_def_id() == def_id
                    }),
                    generic_args,
                ),
                DefTy::Deferred(specs) => {
                    let (spec, generic_args) = specs.iter().find_map(|spec| {
                        Some((spec, self.spec_args(spec, generic_args, caller_def_id)?))
                    })?;
                    (
                        spec.local_def_id,
                        Rc::clone(&spec.cache),
                        Some(spec.mode),
                        generic_args,
                    )
                }
            };

        let key = InstantiationKey {
            generic_args,
            caller_def_id,
        };
        if let Some(rty) = instantiated_ty_cache.borrow().get(&key) {
            return Some(rty.clone());
        }

        let expected = {
            let mut analyzer = self.local_def_analyzer(local_def_id);
            analyzer
                .owner_fn_id(caller_def_id)
                .generic_args(generic_args);
            analyzer.expected_ty()
        };
        instantiated_ty_cache
            .borrow_mut()
            .insert(key, expected.clone());
        tracing::info!(?def_id, rty = %expected.display(), ?generic_args, "deferred def");

        // A generic def's body has been checked once over forall sorts against this contract.
        // Analyzing it again at the instance is needed to define the unknowns minted in
        // `expected` just above (an unannotated or partly annotated contract, or a closure's
        // unknown contract, possibly reached through a predicate's definition), and when the
        // instance is not faithful to the generic check: an `FnMut` closure among the type
        // arguments, whose by-value receiver the instantiated `pre!` reads at a final state equal
        // to the current one. Otherwise the contract is used as instantiated.
        let analyze_body = deferred_ty_mode.is_some_and(|mode| mode.should_analyze())
            && (!is_generic
                || (has_fn_mut_closure(generic_args)
                    && !self.reuse_fn_mut_generic(def_id, &expected, generic_args, caller_def_id))
                || self.may_have_pred_var(&expected, generic_args, caller_def_id));
        if is_generic && !analyze_body {
            self.reused_generic_instances
                .borrow_mut()
                .push((def_id, generic_args, caller_def_id));
        }
        if is_generic && deferred_ty_mode.is_some() {
            tracing::info!(
                ?def_id,
                ?generic_args,
                analyze_body,
                "generic def at an instance"
            );
        }
        if analyze_body {
            let mut body_analyzer = if local_def_id.to_def_id() == def_id {
                let mut body_analyzer = self.local_def_analyzer(local_def_id);
                body_analyzer
                    .owner_fn_id(caller_def_id)
                    .generic_args(generic_args);
                body_analyzer
            } else {
                let body_local_def_id = def_id
                    .as_local()
                    .expect("Analyze mode is only set for deferred defs keyed on a local def");
                // The body is checked against `expected`, which was built under the caller
                // as its owner; analyzing it under the same owner keeps the contracts it reads
                // (a closure argument's, minted while building `expected`) the same instances.
                let mut body_analyzer = self.local_def_analyzer(body_local_def_id);
                body_analyzer
                    .owner_fn_id(caller_def_id)
                    .generic_args(generic_args);
                body_analyzer
            };
            let body_local_def_id = body_analyzer.local_def_id();
            body_analyzer.run(&expected);
            use mir_ty::TypeVisitableExt as _;
            if !generic_args.has_param() {
                self.concrete_instances
                    .borrow_mut()
                    .insert(body_local_def_id);
            }
        }
        Some(expected)
    }

    /// Whether an instance of the generic def `def_id` at `generic_args`, which has an `FnMut`
    /// closure among them, can use its contract as instantiated rather than analyzing the body
    /// again. The generic analysis stands for the instance once the closures obey what it
    /// assumed of their type parameters; those obligations are recorded here. It requires:
    ///
    /// - the def, if `FnMut`-bounded, to be hist_inv-specified ([`Analyzer::is_hist_inv_specified`]);
    /// - each type argument that is an `FnMut` closure to sit at one of its `FnMut`-bounded
    ///   parameters;
    /// - each type argument that nests an `FnMut` closure (`Map<Range, F>` given to `collect`) to
    ///   nest it in local ADTs only, and every `FnMut`-bounded def reachable through them
    ///   ([`Analyzer::fn_mut_defs_reached_through`]) to be hist_inv-specified. Those defs then have
    ///   their own generic analysis emitted, so no def verified per instance is reached only
    ///   through this instance;
    /// - no unknown reachable from the contract, and a known contract for each closure.
    fn reuse_fn_mut_generic(
        &mut self,
        def_id: DefId,
        expected: &rty::RefinedType,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> bool {
        let callee_bounded = fn_mut_bounded_params(self.tcx, def_id);
        if !callee_bounded.is_empty() && !self.is_hist_inv_specified(def_id) {
            return false;
        }
        let generics = self.tcx.generics_of(def_id);
        let mut reached = Vec::new();
        for (idx, arg) in generic_args.iter().enumerate() {
            let Some(ty) = arg.as_type() else {
                continue;
            };
            if !has_fn_mut_closure(self.tcx.mk_args(&[arg])) {
                continue;
            }
            if matches!(ty.kind(), mir_ty::TyKind::Closure(..)) {
                if !callee_bounded.contains(&generics.param_at(idx, self.tcx).def_id) {
                    tracing::info!(
                        ?ty,
                        "FnMut instance analyzed again: closure not at an FnMut-bounded parameter"
                    );
                    return false;
                }
                continue;
            }
            let Some(defs) = self.fn_mut_defs_reached_through(ty) else {
                tracing::info!(
                    ?ty,
                    "FnMut instance analyzed again: closure nested in a type other than a local ADT"
                );
                return false;
            };
            if let Some(def) = defs.iter().find(|def| !self.is_hist_inv_specified(**def)) {
                tracing::info!(
                    ?ty,
                    ?def,
                    "FnMut instance analyzed again: a reachable FnMut-bounded def is verified per instance"
                );
                return false;
            }
            reached.extend(defs);
        }
        if self.may_have_pred_var(expected, generic_args, caller_def_id) {
            tracing::info!(
                ?generic_args,
                "FnMut instance analyzed again: unknowns reachable"
            );
            return false;
        }
        let closures: Vec<_> = generic_args
            .types()
            .flat_map(|ty| ty.walk())
            .filter_map(|arg| arg.as_type())
            .filter(|ty| match ty.kind() {
                mir_ty::TyKind::Closure(_, args) => {
                    args.as_closure().kind() == mir_ty::ClosureKind::FnMut
                }
                _ => false,
            })
            .collect();
        let mut obligations = Vec::new();
        for closure_ty in closures {
            let mir_ty::TyKind::Closure(def_id, args) = closure_ty.kind() else {
                unreachable!()
            };
            let parent_args = self.tcx.mk_args(args.as_closure().parent_args());
            let Some(contract) =
                self.known_function_ty_with_args(*def_id, parent_args, caller_def_id)
            else {
                tracing::info!(
                    ?closure_ty,
                    "FnMut instance analyzed again: closure contract unknown"
                );
                return false;
            };
            let Some(clauses) =
                closure_hist_inv::instance_obligations(closure_ty, &contract, &|from, to| {
                    self.closure_hist_inv_definition(
                        closure_ty,
                        &contract.params[rty::FunctionParamIdx::from_usize(0)]
                            .ty
                            .to_sort()
                            .deref(),
                        from,
                        to,
                    )
                })
            else {
                tracing::info!(
                    ?closure_ty,
                    "FnMut instance analyzed again: precondition unknown"
                );
                return false;
            };
            obligations.push(clauses);
        }
        tracing::info!(?generic_args, "FnMut instance reuses the generic analysis");
        let mut pending = self.fn_mut_instance_obligations.borrow_mut();
        if !callee_bounded.is_empty() {
            pending.reused.insert(def_id);
        }
        pending.reused.extend(reached);
        for (laws, pre) in obligations {
            pending.laws.extend(laws);
            pending.pre.extend(pre);
        }
        true
    }

    /// The local `FnMut`-bounded defs an `FnMut` closure nested in `ty` can reach as the value of
    /// one of their type parameters: the items (and the closures in them) of the local impls
    /// that name an ADT on the path from `ty` to the closure ([`Analyzer::enclosing_impl`]).
    /// `None` if the path passes through
    /// anything but a local ADT, whose impls are not all in view here.
    ///
    /// A generic body receives the closure only inside such an ADT, so it reaches the closure's
    /// type only through the ADT's impls; any other call it makes at the closure's type is made
    /// at its own type parameters and is analyzed within its own generic analysis.
    fn fn_mut_defs_reached_through(&self, ty: mir_ty::Ty<'tcx>) -> Option<Vec<DefId>> {
        let mut adts = Vec::new();
        if !self.collect_adts_to_fn_mut_closures(ty, &mut adts) {
            return None;
        }
        let names_adt = |ty: mir_ty::Ty<'tcx>| {
            ty.walk().any(|arg| {
                arg.as_type().is_some_and(|ty| {
                    matches!(ty.kind(), mir_ty::TyKind::Adt(adt, _) if adts.contains(&adt.did()))
                })
            })
        };
        let defs = self
            .fn_mut_bounded_defs
            .borrow()
            .iter()
            .copied()
            .filter(|def| {
                let Some(impl_did) = self.enclosing_impl(*def) else {
                    return false;
                };
                let self_ty = self.tcx.type_of(impl_did).instantiate_identity();
                let trait_args_name_adt = self
                    .tcx
                    .impl_trait_ref(impl_did)
                    .is_some_and(|tr| tr.instantiate_identity().args.types().any(names_adt));
                names_adt(self_ty) || trait_args_name_adt
            })
            .collect();
        Some(defs)
    }

    /// Collects the ADTs on the paths from `ty` to the `FnMut` closures in it; false if such a
    /// path passes through a type other than a local ADT.
    fn collect_adts_to_fn_mut_closures(&self, ty: mir_ty::Ty<'tcx>, adts: &mut Vec<DefId>) -> bool {
        if !has_fn_mut_closure(self.tcx.mk_args(&[ty.into()])) {
            return true;
        }
        match ty.kind() {
            mir_ty::TyKind::Closure(..) => true,
            mir_ty::TyKind::Adt(adt, args) if adt.did().is_local() => {
                adts.push(adt.did());
                args.types()
                    .all(|ty| self.collect_adts_to_fn_mut_closures(ty, adts))
            }
            _ => false,
        }
    }

    /// The impl whose type parameters `def_id` shares: that of an associated fn, or of the fn a
    /// closure is in. A fn item nested in a body has generics of its own and no such impl; it is
    /// called only from that body, at the body's type parameters.
    fn enclosing_impl(&self, def_id: DefId) -> Option<DefId> {
        let mut cursor = def_id;
        while let Some(parent) = self.tcx.generics_of(cursor).parent {
            if matches!(
                self.tcx.def_kind(parent),
                rustc_hir::def::DefKind::Impl { .. }
            ) {
                return Some(parent);
            }
            cursor = parent;
        }
        None
    }

    /// Pushes the obligations of [`Analyzer::reuse_fn_mut_generic`]: the precondition clauses
    /// always, the `hist_inv!` law clauses when some analysis assumed the laws of a closure type
    /// parameter's relation. That is coarser than tracking which instance reaches which
    /// relation, and only adds checks.
    pub fn emit_fn_mut_instance_obligations(&mut self) {
        let mut pending = self.fn_mut_instance_obligations.borrow_mut();
        let laws = std::mem::take(&mut pending.laws);
        let pre = std::mem::take(&mut pending.pre);
        let mut system = self.system.borrow_mut();
        let laws_assumed = system.forall_preds().any(|pred| {
            pred.inner().starts_with("q_hist_inv_") && !system.laws_of(pred).is_empty()
        });
        let clauses = if laws_assumed { laws } else { Vec::new() };
        for clause in clauses.into_iter().chain(pre) {
            system.push_clause(clause);
        }
    }

    /// Records the `FnMut`-bounded type parameters whose `hist_inv!` relation the specifications
    /// use: those whose relation carries its laws once every contract and predicate definition
    /// has been translated. Taken once, after refinement, so the choice below does not depend
    /// on the order bodies are analyzed in.
    pub fn record_hist_inv_specified_params(&mut self, defs: impl Iterator<Item = LocalDefId>) {
        let system = self.system.borrow();
        let with_laws: HashSet<&str> = system
            .forall_preds()
            .filter(|pred| !system.laws_of(pred).is_empty())
            .map(|pred| pred.inner())
            .collect();
        let mut specified = HashSet::new();
        let mut fn_mut_bounded_defs = Vec::new();
        for def in defs {
            let params = fn_mut_bounded_params(self.tcx, def.to_def_id());
            if self.tcx.def_kind(def).is_fn_like() && !params.is_empty() {
                fn_mut_bounded_defs.push(def.to_def_id());
            }
            for param in params {
                let name = crate::refine::stable_def_id_symbol(self.tcx, param, "q_hist_inv");
                if with_laws.contains(name.as_str()) {
                    specified.insert(param);
                }
            }
        }
        drop(system);
        *self.hist_inv_specified_params.borrow_mut() = specified;
        *self.fn_mut_bounded_defs.borrow_mut() = fn_mut_bounded_defs;
    }

    /// Whether `def_id` has an `FnMut`-bounded type parameter and each of them is one whose
    /// `hist_inv!` relation the specifications use. Only such a def's instances at concrete
    /// closures may use its generic analysis ([`Analyzer::reuse_fn_mut_generic`]); any other
    /// `FnMut`-bounded def is verified per instance (D34).
    pub fn is_hist_inv_specified(&self, def_id: DefId) -> bool {
        let params = fn_mut_bounded_params(self.tcx, def_id);
        let specified = self.hist_inv_specified_params.borrow();
        !params.is_empty() && params.iter().all(|param| specified.contains(param))
    }

    /// Whether an instance has used the contract of `local_def_id` as instantiated, so its
    /// generic analysis stands for that instance and must be emitted.
    pub fn has_reused_instance(&self, local_def_id: LocalDefId) -> bool {
        self.fn_mut_instance_obligations
            .borrow()
            .reused
            .contains(&local_def_id.to_def_id())
    }

    /// Whether the body of `local_def_id` has been analyzed at type arguments that mention no
    /// type parameter, i.e. once per concrete instantiation reached from a call site.
    ///
    /// Every call at concrete type arguments re-analyzes the callee's body for those arguments
    /// (see [`Analyzer::def_ty_with_args`]), so such an instance checks the body against the
    /// contract instantiated at the call site, including the concrete closure contract of an
    /// `FnMut`-bounded type parameter.
    /// The relation of `hist_inv!` at the concrete closure `closure_ty` whose upvars have the sort
    /// `upvars_sort`, between the states `from` and `to`: the one its captures give, and the one
    /// the `hist_inv` clause of its specification writes, if any.
    pub fn closure_hist_inv_definition<V: chc::Var>(
        &self,
        closure_ty: mir_ty::Ty<'tcx>,
        upvars_sort: &chc::Sort,
        from: chc::Term<V>,
        to: chc::Term<V>,
    ) -> chc::Formula<V> {
        let derived = closure_hist_inv::concrete_definition(
            self.tcx,
            closure_ty,
            upvars_sort,
            from.clone(),
            to.clone(),
        );
        if let Some(explicit) =
            self.closure_explicit_hist_inv(closure_ty, upvars_sort, from.clone(), to.clone())
        {
            return derived.and(explicit);
        }
        let positions: Vec<usize> =
            closure_hist_inv::by_value_captures(self.tcx, closure_ty, upvars_sort)
                .into_iter()
                .map(|(idx, _)| idx)
                .collect();
        if positions.is_empty() {
            return derived;
        }
        let relation = self.by_value_hist_inv(closure_ty, upvars_sort);
        derived.and(closure_hist_inv::by_value_related(
            relation, &positions, from, to,
        ))
    }

    /// The unknown relating the by-value captures of `closure_ty`, whose specification writes
    /// no `hist_inv` clause, made with its laws on first use. Where Creusot says nothing of
    /// those captures, the relation is inferred like any other unknown: reflexive and transitive
    /// by these clauses, and implied by each call's postcondition, which includes it.
    fn by_value_hist_inv(
        &self,
        closure_ty: mir_ty::Ty<'tcx>,
        upvars_sort: &chc::Sort,
    ) -> chc::PredVarId {
        let key = (closure_ty, upvars_sort.clone());
        if let Some(relation) = self.by_value_hist_invs.borrow().get(&key) {
            return *relation;
        }
        let sorts: Vec<chc::Sort> =
            closure_hist_inv::by_value_captures(self.tcx, closure_ty, upvars_sort)
                .into_iter()
                .map(|(_, sort)| sort)
                .collect();
        let sig = sorts.iter().chain(&sorts).cloned().collect();
        let relation = self
            .system
            .borrow_mut()
            .new_pred_var(sig, chc::DebugInfo::from_current_span());
        for clause in closure_hist_inv::by_value_relation_laws(relation, &sorts) {
            self.system.borrow_mut().push_clause(clause);
        }
        // Its laws are pushed here and each call's step comes from the closure's body, so a
        // callee whose contract reaches it needs no analysis at the instance to define it.
        self.system.borrow_mut().mark_self_defined(relation);
        self.by_value_hist_invs.borrow_mut().insert(key, relation);
        relation
    }

    /// The relation the `hist_inv` clause of `closure_ty`'s specification writes, between the
    /// states `from` and `to`, with its laws pushed on first use.
    fn closure_explicit_hist_inv<V: chc::Var>(
        &self,
        closure_ty: mir_ty::Ty<'tcx>,
        upvars_sort: &chc::Sort,
        from: chc::Term<V>,
        to: chc::Term<V>,
    ) -> Option<chc::Formula<V>> {
        let mir_ty::TyKind::Closure(def_id, closure_args) = closure_ty.kind() else {
            return None;
        };
        let local_def_id = def_id.as_local()?;
        let formula_def_id = self
            .extract_path_with_attr(local_def_id, &analyze::annot::hist_inv_path_path())?
            .expect_local();
        let generic_args = self.closure_spec_args(formula_def_id, closure_args);
        let owner_fn_id = self.tcx.typeck_root_def_id(*def_id);
        let formula_fn = self
            .formula_fn_with_args(formula_def_id, generic_args, owner_fn_id)
            .expect("hist_inv clause is not a formula function");
        let apply = |from: chc::Term<V>, to: chc::Term<V>| {
            let pair = chc::Term::mut_(from, to);
            formula_fn.formula().clone().subst_var(|_| pair.clone())
        };
        if self
            .explicit_hist_inv_laws
            .borrow_mut()
            .insert((closure_ty, upvars_sort.clone()))
        {
            let related = |from: chc::Term<chc::TermVarIdx>, to: chc::Term<chc::TermVarIdx>| {
                let pair = chc::Term::mut_(from, to);
                formula_fn.formula().clone().subst_var(|_| pair.clone())
            };
            let laws = closure_hist_inv::explicit_laws(closure_ty, upvars_sort, &related);
            for clause in laws {
                self.system.borrow_mut().push_clause(clause);
            }
        }
        Some(apply(from, to))
    }

    /// The generic arguments of a `closure!` specification's formula function at the closure
    /// arguments `closure_args`: none when it is lifted without the enclosing generics, and the
    /// closure's parent arguments when `#[thrust_macros::context]` re-declared them on it.
    fn closure_spec_args(
        &self,
        formula_def_id: LocalDefId,
        closure_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> mir_ty::GenericArgsRef<'tcx> {
        if self.tcx.generics_of(formula_def_id).count() == 0 {
            return self.tcx.mk_args(&[]);
        }
        self.tcx.mk_args(closure_args.as_closure().parent_args())
    }

    pub fn has_concrete_instance(&self, local_def_id: LocalDefId) -> bool {
        self.concrete_instances.borrow().contains(&local_def_id)
    }

    /// Whether a refinement in `rty`, a contract at `generic_args` made from `caller_def_id`,
    /// may name a predicate variable: directly, through the definition of a user-defined
    /// predicate it calls, or through a predicate instance not defined yet. Such an instance's
    /// body can name a predicate variable only through the contract of a closure among
    /// `generic_args`, so it is taken to have one when such a contract does or is not known.
    fn may_have_pred_var(
        &self,
        rty: &rty::RefinedType,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> bool {
        let reach = self.pred_var_reach(rty);
        if reach.found {
            return true;
        }
        if !reach.undefined {
            return false;
        }
        generic_args.types().any(|ty| {
            ty.walk().any(|arg| {
                let Some(mir_ty::TyKind::Closure(closure_def_id, closure_args)) =
                    arg.as_type().map(|ty| ty.kind())
                else {
                    return false;
                };
                let Some(fn_ty) = self.known_function_ty_with_args(
                    *closure_def_id,
                    self.tcx.mk_args(closure_args.as_closure().parent_args()),
                    caller_def_id,
                ) else {
                    return true;
                };
                let reach = self.pred_var_reach(&rty::RefinedType::unrefined(fn_ty.into()));
                reach.found || reach.undefined
            })
        })
    }

    fn pred_var_reach(&self, rty: &rty::RefinedType) -> chc::PredVarReach {
        let system = self.system.borrow();
        let mut reach = chc::PredVarReach::default();
        rty.any_pred(&mut |pred| {
            match pred {
                chc::Pred::Var(id) if !system.is_self_defined(*id) => reach.found = true,
                chc::Pred::UserDefined(p) => reach.join(system.pred_var_reach_of(p)),
                _ => {}
            }
            reach.found
        });
        reach
    }

    pub fn register_formula_fn(&mut self, local_def_id: LocalDefId) {
        tracing::info!(?local_def_id, "register_formula_fn");
        self.formula_fns.insert(
            local_def_id,
            DeferredFormulaFnDef {
                cache: Rc::new(RefCell::new(HashMap::new())),
            },
        );
    }

    pub fn register_basic_block_ty_with_precondition(
        &mut self,
        key: AnalysisKey<'tcx>,
        bb: BasicBlock,
        rty: BasicBlockType,
    ) {
        self.register_basic_block_def(
            key,
            bb,
            BasicBlockDef {
                ty: rty,
                has_precondition: true,
                has_param_types: bb == rustc_middle::mir::START_BLOCK,
            },
        );
    }

    pub fn register_basic_block_ty_without_precondition(
        &mut self,
        key: AnalysisKey<'tcx>,
        bb: BasicBlock,
        rty: BasicBlockType,
    ) {
        self.register_basic_block_def(
            key,
            bb,
            BasicBlockDef {
                ty: rty,
                has_precondition: false,
                has_param_types: false,
            },
        );
    }

    fn register_basic_block_def(
        &mut self,
        key: AnalysisKey<'tcx>,
        bb: BasicBlock,
        def: BasicBlockDef,
    ) {
        tracing::debug!(
            def_id = ?key.local_def_id,
            ?bb,
            rty = %def.ty.display(),
            has_precondition = def.has_precondition,
            "register_basic_block_def",
        );
        self.basic_blocks.entry(key).or_default().insert(bb, def);
    }

    pub fn basic_block_ty(&self, key: AnalysisKey<'tcx>, bb: BasicBlock) -> &BasicBlockType {
        &self.basic_blocks[&key][&bb].ty
    }

    pub fn basic_block_has_param_types(&self, key: AnalysisKey<'tcx>, bb: BasicBlock) -> bool {
        self.basic_blocks[&key][&bb].has_param_types
    }

    pub fn inherit_basic_block_param_types(
        &mut self,
        key: AnalysisKey<'tcx>,
        bb: BasicBlock,
        types: IndexVec<rty::FunctionParamIdx, rty::Type<rty::FunctionParamIdx>>,
    ) {
        let def = self
            .basic_blocks
            .get_mut(&key)
            .unwrap()
            .get_mut(&bb)
            .unwrap();
        if def.has_param_types {
            return;
        }
        for (idx, ty) in types.into_iter_enumerated() {
            def.ty.set_param_type(idx, ty);
        }
        def.has_param_types = true;
    }

    pub fn basic_block_ty_with_precondition(
        &self,
        key: AnalysisKey<'tcx>,
        bb: BasicBlock,
    ) -> &BasicBlockType {
        let def = &self.basic_blocks[&key][&bb];
        assert!(
            def.has_precondition,
            "basic block does not have precondition"
        );
        &def.ty
    }

    pub fn register_well_known_defs(&mut self) {
        let panic_ty = {
            let param = rty::RefinedType::new(
                rty::PointerType::immut_to(rty::Type::string()).into(),
                rty::Refinement::bottom(),
            );
            let ret = rty::RefinedType::new(rty::Type::never(), rty::Refinement::bottom());
            rty::FunctionType::new([param.vacuous()].into_iter().collect(), ret)
        };
        let panic_def_id = self
            .tcx
            .require_lang_item(LangItem::Panic, rustc_span::DUMMY_SP);
        self.register_def(panic_def_id, rty::RefinedType::unrefined(panic_ty.into()));
    }

    pub fn new_env(&self) -> Env {
        refine::Env::new(Rc::clone(&self.enum_defs))
    }

    pub fn crate_analyzer(&mut self) -> crate_::Analyzer<'tcx, '_> {
        crate_::Analyzer::new(self)
    }

    pub fn local_def_analyzer(
        &mut self,
        local_def_id: LocalDefId,
    ) -> local_def::Analyzer<'tcx, '_> {
        local_def::Analyzer::new(self, local_def_id)
    }

    pub fn basic_block_analyzer(
        &mut self,
        key: AnalysisKey<'tcx>,
        bb: BasicBlock,
    ) -> basic_block::Analyzer<'tcx, '_> {
        basic_block::Analyzer::new(self, key, bb)
    }

    pub fn type_builder(&self, def_ids: DefIdCache<'tcx>, owner_fn_id: DefId) -> TypeBuilder<'tcx> {
        TypeBuilder::new(
            self.tcx,
            def_ids,
            owner_fn_id,
            self.type_params.clone(),
            self.closure_type_params.clone(),
            self.system.clone(),
        )
    }

    pub fn solve(&mut self) {
        let mut reverse = HashMap::new();
        for (tp, &idx) in self.type_params.borrow().iter() {
            if let TypeParam::GenericType { local_idx, .. } = tp {
                reverse.insert(idx, *local_idx);
            }
        }
        self.system.borrow_mut().type_params_reverse = reverse;
        if let Err(err) = self.system.borrow().solve() {
            self.tcx.dcx().err(format!("verification error: {:?}", err));
        }
    }

    /// Computes the signature of the function using the given `body`.
    ///
    /// This works like `self.tcx.fn_sig(def_id).instantiate_identity().skip_binder()`,
    /// but extracts parameter and return types directly from the given `body` to obtain a signature that
    /// reflects potential type instantiations happened after `optimized_mir`.
    pub fn fn_sig_with_body(&self, def_id: DefId, body: &mir::Body<'tcx>) -> mir_ty::FnSig<'tcx> {
        let ty = self.tcx.type_of(def_id).instantiate_identity();
        let sig = if let mir_ty::TyKind::Closure(_, substs) = ty.kind() {
            substs.as_closure().sig().skip_binder()
        } else {
            ty.fn_sig(self.tcx).skip_binder()
        };

        self.tcx.mk_fn_sig(
            body.args_iter().map(|arg| body.local_decls[arg].ty),
            body.return_ty(),
            sig.c_variadic,
            sig.safety,
            sig.abi,
        )
    }

    /// Computes the signature of the function.
    ///
    /// This works like `self.tcx.fn_sig(def_id).instantiate_identity().skip_binder()`,
    /// but extracts parameter and return types directly from [`mir::Body`] to obtain a signature that
    /// reflects the actual type of lifted closure functions.
    pub fn fn_sig(&self, def_id: DefId) -> mir_ty::FnSig<'tcx> {
        let body = self.tcx.optimized_mir(def_id);
        self.fn_sig_with_body(def_id, body)
    }

    fn extract_path_with_attr(
        &self,
        local_def_id: LocalDefId,
        attr_path: &[Symbol],
    ) -> Option<DefId> {
        let body = self.tcx.hir_maybe_body_owned_by(local_def_id)?;

        let rustc_hir::ExprKind::Block(block, _) = body.value.kind else {
            return None;
        };
        for stmt in block.stmts {
            if self
                .tcx
                .hir_attrs(stmt.hir_id)
                .iter()
                .all(|attr| !attr.path_matches(attr_path))
            {
                continue;
            }
            let rustc_hir::StmtKind::Semi(expr) = stmt.kind else {
                self.tcx.dcx().span_err(
                    stmt.span,
                    "annotated path is expected to be a semi statement",
                );
                continue;
            };
            let rustc_hir::ExprKind::Path(qpath) = expr.kind else {
                self.tcx.dcx().span_err(
                    expr.span,
                    "annotated path is expected to be a path expression",
                );
                continue;
            };
            let typeck = self.tcx.typeck(local_def_id);
            let rustc_hir::def::Res::Def(_, def_id) = typeck.qpath_res(&qpath, expr.hir_id) else {
                self.tcx.dcx().span_err(
                    expr.span,
                    "annotated path is expected to refer to a definition",
                );
                continue;
            };
            return Some(def_id);
        }
        None
    }

    fn extract_require_annot(
        &self,
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<chc::Formula<rty::FunctionParamIdx>> {
        let formula_def_id =
            self.extract_path_with_attr(local_def_id, &analyze::annot::requires_path_path())?;
        let Some(formula_def_id) = formula_def_id.as_local() else {
            panic!(
                "require annotation with path is expected to refer to a local def, but found: {:?}",
                formula_def_id
            );
        };
        let generic_args = if self.tcx.is_closure_like(local_def_id.to_def_id()) {
            self.closure_spec_args(formula_def_id, generic_args)
        } else {
            generic_args
        };
        let Some(formula_fn) = self.formula_fn_with_args(formula_def_id, generic_args, owner_fn_id)
        else {
            panic!(
                "require annotation {:?} is not a formula function",
                formula_def_id
            );
        };
        Some(formula_fn.to_require_formula())
    }

    fn extract_ensure_annot(
        &self,
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<chc::Formula<rty::RefinedTypeVar<rty::FunctionParamIdx>>> {
        let formula_def_id =
            self.extract_path_with_attr(local_def_id, &analyze::annot::ensures_path_path())?;
        let Some(formula_def_id) = formula_def_id.as_local() else {
            panic!(
                "ensure annotation with path is expected to refer to a local def, but found: {:?}",
                formula_def_id
            );
        };
        let generic_args = if self.tcx.is_closure_like(local_def_id.to_def_id()) {
            self.closure_spec_args(formula_def_id, generic_args)
        } else {
            generic_args
        };
        let Some(formula_fn) = self.formula_fn_with_args(formula_def_id, generic_args, owner_fn_id)
        else {
            panic!(
                "ensure annotation {:?} is not a formula function",
                formula_def_id
            );
        };
        Some(formula_fn.to_ensure_formula())
    }

    /// Collects every `#[thrust::refinement_path(..)]` path statement in the
    /// function body, returning each `(type position, formula_fn DefId)`.
    fn extract_refinement_paths(
        &self,
        local_def_id: LocalDefId,
    ) -> Vec<(rty::TypePosition, DefId)> {
        let mut out = Vec::new();
        let Some(body) = self.tcx.hir_maybe_body_owned_by(local_def_id) else {
            return out;
        };
        let rustc_hir::ExprKind::Block(block, _) = body.value.kind else {
            return out;
        };
        let attr_path = analyze::annot::refinement_path_path();
        let typeck = self.tcx.typeck(local_def_id);
        for stmt in block.stmts {
            let Some(attr) = self
                .tcx
                .hir_attrs(stmt.hir_id)
                .iter()
                .find(|attr| attr.path_matches(&attr_path))
            else {
                continue;
            };
            let ts = analyze::annot::extract_annot_tokens(attr.clone());
            let position = analyze::annot::parse_type_position(&ts);

            let rustc_hir::StmtKind::Semi(expr) = stmt.kind else {
                self.tcx.dcx().span_err(
                    stmt.span,
                    "annotated path is expected to be a semi statement",
                );
                continue;
            };
            let rustc_hir::ExprKind::Path(qpath) = expr.kind else {
                self.tcx.dcx().span_err(
                    expr.span,
                    "annotated path is expected to be a path expression",
                );
                continue;
            };
            let rustc_hir::def::Res::Def(_, def_id) = typeck.qpath_res(&qpath, expr.hir_id) else {
                self.tcx.dcx().span_err(
                    expr.span,
                    "annotated path is expected to refer to a definition",
                );
                continue;
            };
            out.push((position, def_id));
        }
        out
    }

    /// Resolves every `#[thrust::refinement_path(..)]` annotation into a
    /// positioned refinement, by translating the referenced formula function.
    pub fn extract_refinement_annots(
        &self,
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Vec<(rty::TypePosition, rty::Refinement<rty::FunctionParamIdx>)> {
        let mut out = Vec::new();
        for (position, def_id) in self.extract_refinement_paths(local_def_id) {
            let Some(formula_def_id) = def_id.as_local() else {
                panic!(
                    "refinement_path annotation is expected to refer to a local def, but found: {:?}",
                    def_id
                );
            };
            let Some(formula_fn) =
                self.formula_fn_with_args(formula_def_id, generic_args, owner_fn_id)
            else {
                panic!(
                    "refinement_path annotation {:?} is not a formula function",
                    formula_def_id
                );
            };
            out.push((position, formula_fn.to_refinement()));
        }
        out
    }

    /// Whether the given `def_id` corresponds to a method of a trait.
    /// Whether the given `def_id` corresponds to a method of one of the `Fn` traits.
    fn is_fn_trait_method(&self, def_id: DefId) -> bool {
        self.tcx
            .opt_associated_item(def_id)
            .and_then(|item| item.trait_container(self.tcx))
            .and_then(|trait_did| self.tcx.fn_trait_kind_from_def_id(trait_did))
            .is_some()
    }
}
