//! Analysis of Rust MIR to generate a CHC system.
//!
//! The [`Analyzer`] generates subtyping constraints in the form of CHCs ([`chc::System`]).
//! The entry point is [`crate_::Analyzer::run`], followed by [`local_def::Analyzer::run`]
//! and [`basic_block::Analyzer::run`], while accumulating the necessary information in
//! [`Analyzer`]. Once [`chc::System`] is collected for the entire input, it invokes an external
//! CHC solver with the [`Analyzer::solve`] and subsequently reports the result.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
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
mod derive;
pub(crate) mod derived_pred;
mod did_cache;
mod extern_spec;
mod fn_mut_reuse;
mod lemma;
mod local_def;
mod model_eq;
mod pred_inst;
mod reconstruct_slice_indexing;
pub(crate) mod selection;
mod two_phase_borrow;
pub mod unanalyzed_entry;

// TODO: organize structure and remove cross dependency between refine
pub use did_cache::DefIdCache;

// Also the paths siblings use: analyze::{predicate_typing_env, trait_bounds,
// fn_mut_bounded_params}.
use closure_hist_inv::HistInvRelations;
use extern_spec::{predicate_typing_env, trait_bounds, SpecAssumptions};
use fn_mut_reuse::{fn_mut_bounded_params, has_fn_mut_closure, FnMutReuse};

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

/// The `drop` method of `ty`'s `Drop` impl, when `ty` is an ADT whose impl is in the crate.
pub fn local_destructor(tcx: TyCtxt<'_>, ty: mir_ty::Ty<'_>) -> Option<DefId> {
    let adt = ty.ty_adt_def()?;
    let dtor = tcx.adt_destructor(adt.did())?;
    dtor.did.is_local().then_some(dtor.did)
}

/// Whether dropping a value of `ty` may run a destructor of the crate.
pub fn drop_runs_local_destructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    reaches(tcx, typing_env, ty, |ty| {
        if local_destructor(tcx, ty).is_some() {
            return Reach::Found;
        }
        if ty.needs_drop(tcx, typing_env) {
            Reach::Parts
        } else {
            Reach::Stop
        }
    })
}

/// Whether dropping the parts of a value of `ty`, which its drop glue drops after its own
/// destructor, may run a destructor of the crate.
pub fn drop_of_parts_runs_local_destructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    ty.needs_drop(tcx, typing_env)
        && held_tys(tcx, typing_env, ty)
            .into_iter()
            .any(|part| drop_runs_local_destructor(tcx, typing_env, part))
}

/// Whether a value of `ty` may hold a `&mut`, whose prophecy its drop would resolve.
pub fn may_hold_mut_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> bool {
    reaches(tcx, typing_env, ty, |ty| match ty.kind() {
        mir_ty::TyKind::Ref(_, _, m) if m.is_mut() => Reach::Found,
        mir_ty::TyKind::Ref(..) | mir_ty::TyKind::RawPtr(..) => Reach::Stop,
        _ => Reach::Parts,
    })
}

/// What [`reaches`] does at a type.
enum Reach {
    Found,
    Parts,
    Stop,
}

/// The number of types [`reaches`] looks at before it gives up and answers yes, which every caller
/// takes as the cautious answer. A polymorphically recursive type
/// (`struct N<T>(Option<Box<N<(T, T)>>>)`) holds unboundedly many.
const MAX_REACHED_TYS: usize = 1024;

/// Whether `visit` finds a type among `ty` and the types it holds ([`held_tys`]), looking into the
/// parts of a type where it says so.
fn reaches<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
    mut visit: impl FnMut(mir_ty::Ty<'tcx>) -> Reach,
) -> bool {
    let mut visited = HashSet::new();
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        if !visited.insert(ty) {
            continue;
        }
        if visited.len() > MAX_REACHED_TYS {
            return true;
        }
        match visit(ty) {
            Reach::Found => return true,
            Reach::Parts => pending.extend(held_tys(tcx, typing_env, ty)),
            Reach::Stop => {}
        }
    }
    false
}

/// The types of the values a value of `ty` holds or refers to: the fields of every variant of an
/// ADT and its type arguments, the components of a tuple, an array or a closure, and the pointee
/// of a reference or a pointer. Field types are normalized, so an associated type names the type
/// it stands for.
pub fn held_tys<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> Vec<mir_ty::Ty<'tcx>> {
    match ty.kind() {
        mir_ty::TyKind::Adt(adt, args) => adt
            .all_fields()
            .map(|field| normalize(tcx, typing_env, field.ty(tcx, args)))
            .chain(args.types())
            .collect(),
        mir_ty::TyKind::Tuple(tys) => tys.to_vec(),
        mir_ty::TyKind::Array(elem, _) | mir_ty::TyKind::Slice(elem) => vec![*elem],
        mir_ty::TyKind::Closure(_, args) => args.as_closure().upvar_tys().to_vec(),
        mir_ty::TyKind::Ref(_, pointee, _) | mir_ty::TyKind::RawPtr(pointee, _) => vec![*pointee],
        _ => Vec::new(),
    }
}

/// The types of the fields of a tuple or a struct, normalized.
pub fn field_tys<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> Option<Vec<mir_ty::Ty<'tcx>>> {
    match ty.kind() {
        mir_ty::TyKind::Tuple(tys) => Some(tys.to_vec()),
        mir_ty::TyKind::Adt(adt, args) if adt.is_struct() => Some(
            adt.all_fields()
                .map(|field| normalize(tcx, typing_env, field.ty(tcx, args)))
                .collect(),
        ),
        _ => None,
    }
}

fn normalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: mir_ty::TypingEnv<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> mir_ty::Ty<'tcx> {
    tcx.try_normalize_erasing_regions(typing_env, ty)
        .unwrap_or(ty)
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

/// Whether `def_id` comes from the injected `std.rs`.
pub fn is_injected_std(tcx: mir_ty::TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let span = tcx.def_span(def_id);
    matches!(
        tcx.sess.source_map().span_to_filename(span),
        rustc_span::FileName::Custom(name) if name == crate::INJECTED_STD_FILE_NAME
    )
}

/// Whether `def_id` is `#[thrust::ignored]`, so that its body is not analyzed.
pub fn is_ignored(tcx: mir_ty::TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.get_attrs_by_path(def_id, &annot::ignored_path())
        .next()
        .is_some()
}

/// Whether `def_id` is a function of the crate, not of the injected `std.rs`, that is ignored:
/// nothing checks its body against the specification of the trait method it implements.
pub fn is_ignored_crate_fn(tcx: mir_ty::TyCtxt<'_>, def_id: DefId) -> bool {
    def_id
        .as_local()
        .is_some_and(|local| !is_injected_std(tcx, local))
        && is_ignored(tcx, def_id)
}

/// Stops at a call that resolves to an ignored function of the crate, which has no checked type.
pub fn fatal_ignored_call<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    def_id: DefId,
    args: mir_ty::GenericArgsRef<'tcx>,
) -> ! {
    tcx.dcx().fatal(format!(
        "`{}` is `#[thrust::ignored]`, so a call of it has no checked type",
        tcx.def_path_str_with_args(def_id, args),
    ))
}

/// Whether code on a path through the program ([`Analyzer::stop_ignored_reached`]) is verified
/// code, which may not run an ignored function, or trusted code, which may.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    Verified,
    Trusted,
}

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
    GenericType { param_def_id: DefId, local_idx: u32 },
    /// A projection that does not normalize: the associated item, its arguments' types and their
    /// names ([`refine::TypeBuilder::generic_args_symbol`]), which tell apart arguments of one sort.
    AssocType(DefId, Vec<rty::Type<rty::Closed>>, String),
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
    /// The predicate instances whose bodies are being translated, innermost last.
    defining_predicates: Rc<RefCell<Vec<PredicateInstanceKey<'tcx>>>>,

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
    /// The generic defs whose bodies were analyzed at concrete arguments, and those arguments.
    analyzed_instances: RefCell<Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)>>,
    /// See [`HistInvRelations`].
    hist_inv_relations: HistInvRelations<'tcx>,
    /// See [`FnMutReuse`].
    fn_mut_reuse: FnMutReuse,
    /// See [`SpecAssumptions`].
    spec_assumptions: SpecAssumptions<'tcx>,
    /// The instances `(def, generic args, caller)` that use a generic def's contract as
    /// instantiated; see [`Analyzer::check_reused_spec_bounds`].
    reused_generic_instances: RefCell<Vec<(DefId, mir_ty::GenericArgsRef<'tcx>, DefId)>>,
    /// The types of the functions each basic block calls, recorded only when
    /// [`candidate_atoms_enabled`], whose contracts give a loop head candidate atoms.
    called_fn_tys: HashMap<(AnalysisKey<'tcx>, BasicBlock), Vec<rty::FunctionType>>,
    /// The local methods of trait impls that carry a contract of their own, given by an
    /// extern-spec wrapper; see [`Analyzer::has_own_impl_contract`].
    impl_methods_with_own_contract: rustc_data_structures::fx::FxIndexSet<DefId>,
    /// Each derived predicate declared at an impl, by symbol; see [`derived_pred`].
    derived_preds: Rc<RefCell<HashMap<chc::UserDefinedPred, derived_pred::DerivedAt>>>,
    /// Each trait law checked for an impl that inherits it, as (impl, law).
    inherited_laws_checked: Rc<RefCell<HashSet<(DefId, DefId)>>>,
    /// The local generic impls whose laws are checked at each instance; see
    /// [`derived_pred::per_instance_law_impls`].
    pub(crate) per_instance_law_impls: HashSet<DefId>,
    /// Each trait law checked at the trait arguments of an instance of such an impl, as (law,
    /// trait arguments).
    instance_laws_checked: RefCell<HashSet<(DefId, mir_ty::GenericArgsRef<'tcx>)>>,
    /// Each use of a trait law's contract while there are such impls, as (law, arguments).
    law_uses: RefCell<Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)>>,
    /// The template being made now, for the predicate variables allocated meanwhile.
    template_site: Option<TemplateSite>,
    /// The variable each argument of a template's predicate variable is, by the variable.
    template_vars: HashMap<chc::PredVarId, Vec<Option<chc::debug::ErasedVar>>>,
    /// Where each template's predicate variable was made.
    template_sites: HashMap<chc::PredVarId, TemplateSite>,
    /// Where the written contract of each function is annotated, for the report.
    contract_annotations: HashMap<DefId, ContractAnnotations>,
    /// Where the written invariant of each loop, by its header, is annotated, for the report.
    invariant_annotations: HashMap<(LocalDefId, BasicBlock), Vec<rustc_span::Span>>,
    /// The fn-like defs whose bodies are trusted rather than analyzed.
    trusted_bodies: HashSet<LocalDefId>,
    /// The closures each analyzed body hands over to code Thrust does not analyze, by the body
    /// and the function called.
    handovers: Vec<(DefId, DefId, unanalyzed_entry::HandedOver)>,
    /// What the analysis did with the body of each function, for the report.
    body_checks: BodyChecks,
}

/// What the analysis did with the body of each function, shared by the analyzers that decide it.
#[derive(Debug, Clone, Default)]
pub struct BodyChecks(Rc<RefCell<HashMap<LocalDefId, BodyCheck>>>);

impl BodyChecks {
    /// Keeps what the analysis did with the body of `def`. An analysis of the body overrides any
    /// earlier decision (a generic def left to its instances, then analyzed at one), and is
    /// overridden by none; otherwise the first decision is kept.
    pub fn record(&self, def: LocalDefId, check: BodyCheck) {
        let mut checks = self.0.borrow_mut();
        let kept = checks.entry(def).or_insert(check);
        if check == BodyCheck::Checked {
            *kept = check;
        }
    }

    pub fn get(&self, def: LocalDefId) -> Option<BodyCheck> {
        self.0.borrow().get(&def).copied()
    }

    pub fn snapshot(&self) -> HashMap<LocalDefId, BodyCheck> {
        self.0.borrow().clone()
    }
}

/// What the analysis did with the body of a function, recorded where it decides it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyCheck {
    /// Analyzed, over its type parameters or at an instance: its clauses are in the system.
    Checked,
    /// Not analyzed, its written contract assumed.
    Trusted(&'static str),
    /// Not analyzed, and verified code is checked not to run it.
    Ignored(&'static str),
    /// Outside `THRUST_VERIFY_ONLY`, so not analyzed, its written contract assumed.
    Unselected(&'static str),
    /// Not analyzed for another reason.
    NotAnalyzed(&'static str),
    /// A specification function (a predicate, a formula, an extern spec), which is no code.
    Specification,
}

impl BodyCheck {
    pub fn status(self) -> &'static str {
        match self {
            BodyCheck::Checked => "checked",
            BodyCheck::Trusted(_) => "trusted",
            BodyCheck::Ignored(_) => "ignored",
            BodyCheck::Unselected(_) => "unselected",
            BodyCheck::NotAnalyzed(_) | BodyCheck::Specification => "not_analyzed",
        }
    }

    pub fn reason(self) -> Option<&'static str> {
        match self {
            BodyCheck::Checked => None,
            BodyCheck::Trusted(reason)
            | BodyCheck::Ignored(reason)
            | BodyCheck::Unselected(reason)
            | BodyCheck::NotAnalyzed(reason) => Some(reason),
            BodyCheck::Specification => Some("a specification function"),
        }
    }
}

/// Whether `expr` is the literal `true`.
fn is_true(expr: &rustc_hir::Expr<'_>) -> bool {
    let rustc_hir::ExprKind::Lit(lit) = expr.kind else {
        return false;
    };
    matches!(lit.node, rustc_ast::LitKind::Bool(true))
}

/// The span covering the code of `expr` the program writes, if a macro made `expr` from some.
fn user_span(expr: &rustc_hir::Expr<'_>) -> Option<rustc_span::Span> {
    struct Written(Option<rustc_span::Span>);
    impl<'v> rustc_hir::intravisit::Visitor<'v> for Written {
        fn visit_expr(&mut self, e: &'v rustc_hir::Expr<'v>) {
            if !e.span.from_expansion() {
                self.0 = Some(self.0.map_or(e.span, |all| all.to(e.span)));
            }
            rustc_hir::intravisit::walk_expr(self, e);
        }
    }
    let mut written = Written(None);
    rustc_hir::intravisit::Visitor::visit_expr(&mut written, expr);
    written.0
}

/// The spans of the clauses `expr` conjoins as the program writes them, but those that are
/// `true`. A macro conjoins each clause to those before it (the specification attributes
/// starting from `true`); a clause it rewrote is spanned by the code of it the program writes, or
/// else by the conjunction, which a specification attribute spans by itself.
fn written_clauses(expr: &rustc_hir::Expr<'_>) -> Vec<rustc_span::Span> {
    use rustc_hir::{BinOpKind, ExprKind};
    match expr.kind {
        ExprKind::Binary(op, before, clause)
            if expr.span.from_expansion() && op.node == BinOpKind::And =>
        {
            let this = (!is_true(clause)).then(|| user_span(clause).unwrap_or(expr.span));
            [written_clauses(before), this.into_iter().collect()].concat()
        }
        ExprKind::DropTemps(e) => written_clauses(e),
        _ if is_true(expr) => Vec::new(),
        _ => vec![user_span(expr).unwrap_or(expr.span)],
    }
}

/// The annotations a function's written contract is read from, by the spans of their companion
/// functions: `requires` and the parameters' refinements, `ensures` and the result's.
#[derive(Debug, Clone, Default)]
pub struct ContractAnnotations {
    pub requires: Vec<rustc_span::Span>,
    pub ensures: Vec<rustc_span::Span>,
    /// The refinements written in each parameter's type, by the parameter.
    pub params: BTreeMap<rty::FunctionParamIdx, Vec<rustc_span::Span>>,
}

/// Whether loop heads get candidate atoms (`THRUST_CANDIDATE_ATOMS`, see
/// [`chc::CandidateAtomsMode`]).
pub fn candidate_atoms_enabled() -> bool {
    chc::CandidateAtomsMode::from_env() != chc::CandidateAtomsMode::Off
}

impl<'tcx> crate::refine::TemplateRegistry for Analyzer<'tcx> {
    fn register_template<V: chc::Var>(&mut self, tmpl: rty::Template<V>) -> rty::RefinedType<V> {
        tmpl.into_refined_type(|pred_sig, args| {
            let pred_var = self.generate_pred_var(pred_sig);
            self.template_vars.insert(pred_var, args);
            if let Some(site) = self.template_site {
                self.template_sites.insert(pred_var, site);
            }
            pred_var
        })
    }
}

/// `THRUST_SPLIT`: the number of parts of the system solved at a time, when the parts are solved
/// on their own; `None` when unset, empty or `0`, and an error for anything but a number.
fn split_jobs() -> Result<Option<usize>, String> {
    let Ok(value) = std::env::var("THRUST_SPLIT") else {
        return Ok(None);
    };
    match value.trim() {
        "" => Ok(None),
        jobs => match jobs.parse::<usize>() {
            Ok(0) => Ok(None),
            Ok(n) => Ok(Some(n)),
            Err(_) => Err(format!("`THRUST_SPLIT`: `{jobs}` is no number of parts")),
        },
    }
}

/// Where the analysis makes a template, and so its predicate variables: a function's contract,
/// a block's type, or the code of a block (the result of a call it makes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateSite {
    Contract(LocalDefId),
    Block(LocalDefId, BasicBlock),
    Code(LocalDefId, BasicBlock),
}

impl TemplateSite {
    pub fn def(self) -> LocalDefId {
        match self {
            TemplateSite::Contract(def)
            | TemplateSite::Block(def, _)
            | TemplateSite::Code(def, _) => def,
        }
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Makes the templates made until [`Analyzer::leave_template_site`] those of `site`, and
    /// returns the site that was current.
    pub fn enter_template_site(&mut self, site: TemplateSite) -> Option<TemplateSite> {
        self.template_site.replace(site)
    }

    pub fn leave_template_site(&mut self, previous: Option<TemplateSite>) {
        self.template_site = previous;
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
            defining_predicates: Default::default(),
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
            analyzed_instances: Default::default(),
            hist_inv_relations: Default::default(),
            fn_mut_reuse: Default::default(),
            spec_assumptions: Default::default(),
            reused_generic_instances: Default::default(),
            called_fn_tys: Default::default(),
            impl_methods_with_own_contract: Default::default(),
            derived_preds: Default::default(),
            inherited_laws_checked: Default::default(),
            per_instance_law_impls: Default::default(),
            instance_laws_checked: Default::default(),
            law_uses: Default::default(),
            template_site: None,
            template_vars: Default::default(),
            template_sites: Default::default(),
            contract_annotations: Default::default(),
            invariant_annotations: Default::default(),
            trusted_bodies: Default::default(),
            handovers: Default::default(),
            body_checks: Default::default(),
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
                    name: refine::variant_symbol(&name, variant.name),
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

    pub fn register_impl_method_with_own_contract(&mut self, def_id: DefId) {
        self.impl_methods_with_own_contract.insert(def_id);
    }

    /// Whether `def_id` is a local method of a trait impl with a contract of its own. A call
    /// resolved to it uses that contract, which refines the trait's (`check_impl_refinements` in
    /// [`crate_`]); one without its own contract takes the trait's.
    pub fn has_own_impl_contract(&self, def_id: DefId) -> bool {
        self.impl_methods_with_own_contract.contains(&def_id)
    }

    /// Stops if a function Thrust verifies can run an ignored function of the crate, as Verus's
    /// verified code may not use an `#[verifier::external]` item. An ignored function is
    /// invisible to the analysis, so a contract the verified code relies on it to meet (the
    /// trait's specification for `S::eq` that `<&S as PartialEq>::eq` or `vec![x; n]` takes) is
    /// not checked.
    ///
    /// The roots are the monomorphic functions of the crate (`roots`: those Thrust verifies, the
    /// trusted ones and the entry function), the instances Thrust analyzed or reused a generic
    /// contract at, the calls a generic verified body makes at concrete arguments
    /// (`generic_roots`), and the runtime's `start` at `main`'s return type, each in the mode its
    /// function has. From them the calls, trait methods, vtables, drop
    /// glue, function pointers and closures each instance uses (`items_of_instance`, as rustc's
    /// monomorphization collector) are followed, into std code and trusted bodies too, each
    /// instance in a mode ([`Mode`]): that of the crate function it is (`crate_mode`), or of the
    /// path it is reached on. A trusted body may run an ignored function itself, as Verus's
    /// `external_body` and Creusot's and Prusti's `#[trusted]` may, but a verified function it
    /// runs may not. A generic trusted instance that verified code runs has its contract relied on,
    /// which holds only where the code its type parameters are instantiated with meets its
    /// specification, as for Creusot's trusted contracts, so everything its body runs at the
    /// instance is verified code; a closure written in a generic trusted body is verified as that
    /// body is, and a shim passes the mode to the instance inside it. A
    /// non-generic trusted body is trusted throughout. A function pointer, trait object or
    /// closure that a trusted body hands out carries the trusted mode: calling it is the trusted
    /// author's responsibility. Static initializers are not followed: verified code cannot read a
    /// static (the analysis stops), and a static has no type parameters, so what a trusted body
    /// reaches through one is its author's fixed choice. An instance is followed once per mode it
    /// is reached in. This over-approximates what the verified functions can run: an instance
    /// reached only on a path to a panic counts.
    pub fn stop_ignored_reached(
        &self,
        roots: Vec<mir_ty::Instance<'tcx>>,
        generic_roots: Vec<DefId>,
        crate_mode: impl Fn(DefId) -> Option<Mode>,
    ) {
        let mut parent = HashMap::new();
        let mut pending = std::collections::VecDeque::new();
        let roots = self.walk_roots(roots, generic_roots, |def_id| {
            crate_mode(def_id) == Some(Mode::Verified)
        });
        for root in roots {
            let key = (root, crate_mode(root.def_id()).unwrap_or(Mode::Verified));
            if parent.insert(key, None).is_none() {
                pending.push_back(key);
            }
        }
        let mut reached = Vec::new();
        while let Some((instance, mode)) = pending.pop_front() {
            if is_ignored_crate_fn(self.tcx, instance.def_id()) {
                if mode == Mode::Verified {
                    reached.push((instance, (instance, mode)));
                }
                continue;
            }
            if !self.runs_body(instance) {
                continue;
            }
            for callee in self.callees(instance) {
                // A generic trusted instance that verified code runs is verified code: its contract
                // holds only where the code its type parameters bring meets its specification.
                let callee_mode = match crate_mode(callee.def_id()) {
                    Some(Mode::Trusted) if mode == Mode::Verified && self.is_generic(callee) => {
                        Mode::Verified
                    }
                    Some(callee_mode) => callee_mode,
                    None => mode,
                };
                let key = (callee, callee_mode);
                if let std::collections::hash_map::Entry::Vacant(entry) = parent.entry(key) {
                    entry.insert(Some((instance, mode)));
                    pending.push_back(key);
                }
            }
        }
        let Some(&(first, key)) = reached.first() else {
            return;
        };
        let mut path = Vec::new();
        let mut cursor = Some(key);
        while let Some(current) = cursor {
            path.push(current.0.to_string());
            cursor = parent.get(&current).copied().flatten();
        }
        path.reverse();
        let mut diag = self.tcx.dcx().struct_span_fatal(
            self.tcx.def_span(first.def_id()),
            format!(
                "`{first}` is `#[thrust::ignored]`, so a call of it has no checked type, but a \
                 verified function can run it"
            ),
        );
        diag.note(format!("reached through {}", path.join(" -> ")));
        for (other, _) in &reached[1..] {
            diag.span_note(
                self.tcx.def_span(other.def_id()),
                format!("`{other}` is ignored and reached too"),
            );
        }
        diag.emit()
    }

    /// The roots of a walk over what the crate can run: `roots`, the runtime's `start` at `main`'s
    /// return type, the instances of generic defs Thrust analyzed or reused a contract at whose
    /// def `verified` holds of, and the calls the generic bodies `generic_roots` make at concrete
    /// arguments.
    pub fn walk_roots(
        &self,
        roots: Vec<mir_ty::Instance<'tcx>>,
        generic_roots: Vec<DefId>,
        verified: impl Fn(DefId) -> bool,
    ) -> Vec<mir_ty::Instance<'tcx>> {
        let verified_instances = self
            .reused_and_analyzed_instances()
            .into_iter()
            .filter(|instance| verified(instance.def_id()));
        roots
            .into_iter()
            .chain(self.start_instance())
            .chain(verified_instances)
            .chain(
                generic_roots
                    .into_iter()
                    .flat_map(|def_id| self.concrete_mentions(def_id)),
            )
            .collect()
    }

    /// Whether `instance` is of a generic def, whose body runs code its arguments choose. A
    /// closure is as generic as the function it is written in; its own synthetic parameters are
    /// fixed by that function.
    fn is_generic(&self, instance: mir_ty::Instance<'tcx>) -> bool {
        let root = self.tcx.typeck_root_def_id(instance.def_id());
        self.tcx
            .generics_of(root)
            .requires_monomorphization(self.tcx)
    }

    /// The functions `instance`'s body uses.
    fn callees(&self, instance: mir_ty::Instance<'tcx>) -> Vec<mir_ty::Instance<'tcx>> {
        use rustc_middle::mir::mono::{CollectionMode, MonoItem};

        let (used, _) = self
            .tcx
            .items_of_instance((instance, CollectionMode::UsedItems));
        used.iter()
            .filter_map(|item| match item.node {
                MonoItem::Fn(callee) => Some(callee),
                _ => None,
            })
            .collect()
    }

    /// The `start` lang item at `main`'s return type, which runs `main` and reports what it
    /// returns (`Termination::report`, which prints an `Err` with `Debug`), as rustc's collector
    /// roots it.
    fn start_instance(&self) -> Option<mir_ty::Instance<'tcx>> {
        let (main, _) = self.tcx.entry_fn(())?;
        let start = self.tcx.lang_items().start_fn()?;
        let ret = self.tcx.fn_sig(main).instantiate_identity().output();
        let ret = self.tcx.instantiate_bound_regions_with_erased(ret);
        let args = self.tcx.mk_args(&[ret.into()]);
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        mir_ty::Instance::try_resolve(self.tcx, typing_env, start, args)
            .ok()
            .flatten()
    }

    /// The instances of generic defs that Thrust analyzed, or whose contract it reused, at
    /// concrete arguments.
    fn reused_and_analyzed_instances(&self) -> Vec<mir_ty::Instance<'tcx>> {
        use mir_ty::TypeVisitableExt as _;

        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        self.reused_generic_instances
            .borrow()
            .iter()
            .map(|(def_id, args, _)| (*def_id, *args))
            .chain(self.analyzed_instances.borrow().iter().copied())
            .filter(|(_, args)| !args.has_param())
            .filter_map(|(def_id, args)| {
                mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, args)
                    .ok()
                    .flatten()
            })
            .collect()
    }

    /// The functions and drop glue a generic body mentions at concrete arguments, which are the
    /// same at every instance of it.
    fn concrete_mentions(&self, def_id: DefId) -> Vec<mir_ty::Instance<'tcx>> {
        use mir_ty::TypeVisitableExt as _;
        use rustc_middle::mir::MentionedItem;

        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let body = self.tcx.optimized_mir(def_id);
        body.mentioned_items()
            .iter()
            .filter_map(|item| match item.node {
                MentionedItem::Fn(ty) if !ty.has_param() => {
                    let mir_ty::FnDef(callee, args) = *ty.kind() else {
                        return None;
                    };
                    mir_ty::Instance::try_resolve(self.tcx, typing_env, callee, args)
                        .ok()
                        .flatten()
                }
                MentionedItem::Drop(ty) if !ty.has_param() => {
                    Some(mir_ty::Instance::resolve_drop_in_place(self.tcx, ty))
                }
                _ => None,
            })
            .collect()
    }

    /// Whether the body of `instance` is followed: not a virtual call or an intrinsic, which have
    /// none, not a foreign item, and one whose MIR is available.
    fn runs_body(&self, instance: mir_ty::Instance<'tcx>) -> bool {
        let def_id = instance.def_id();
        match instance.def {
            mir_ty::InstanceKind::Virtual(..) | mir_ty::InstanceKind::Intrinsic(_) => false,
            mir_ty::InstanceKind::Item(_) => {
                !self.tcx.is_foreign_item(def_id) && self.tcx.is_mir_available(def_id)
            }
            _ => true,
        }
    }

    /// Whether `def_id` is a trait's `#[thrust_macros::predicate(derived)]`. Stops if the marker
    /// is on anything but a trait item.
    pub fn is_derived_predicate(&self, def_id: DefId) -> bool {
        let derived = self
            .tcx
            .get_attrs_by_path(def_id, &analyze::annot::derived_path())
            .next()
            .is_some();
        if derived && self.tcx.trait_of_assoc(def_id).is_none() {
            self.tcx.dcx().span_fatal(
                self.tcx.def_span(def_id),
                format!(
                    "`#[thrust_macros::predicate(derived)]` declares a trait's predicate that an \
                     impl may leave out, but `{}` is not declared in a trait",
                    self.tcx.def_path_str(def_id)
                ),
            );
        }
        derived
    }

    /// Declares `symbol`, the derived predicate `pred_def_id` of a trait, at the impl the
    /// trait arguments of `generic_args` select.
    pub fn declare_derived_pred(
        &self,
        symbol: chc::UserDefinedPred,
        sig: chc::UserDefinedPredSig,
        pred_def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) {
        let per_instance = crate_::per_instance_generics();
        let at = derived_pred::DerivedAt::new(self.tcx, pred_def_id, generic_args, per_instance)
            .unwrap_or_else(|| {
                self.tcx.dcx().span_fatal(
                    self.tcx.def_span(owner_fn_id),
                    format!(
                        "the derived predicate `{}` is left undefined by a generic impl, which \
                         needs each instance analyzed (`THRUST_PER_INSTANCE_GENERICS=1`); define \
                         it in the impl",
                        self.tcx.def_path_str_with_args(pred_def_id, generic_args)
                    ),
                )
            });
        self.system
            .borrow_mut()
            .push_derived_pred(symbol.clone(), sig);
        self.derived_preds.borrow_mut().insert(symbol, at);
    }

    /// Whether `def_id` is a `#[thrust::law]` declared in a local trait.
    fn is_trait_law(&self, def_id: DefId) -> bool {
        self.tcx.trait_of_assoc(def_id).is_some_and(|t| {
            self.trait_laws
                .borrow()
                .get(&t)
                .is_some_and(|laws| laws.contains(&def_id))
        })
    }

    /// Records that the trait law `law`, inherited by `impl_def_id`, was checked for it.
    pub fn inherited_law_checked(&self, impl_def_id: DefId, law: DefId) {
        self.inherited_laws_checked
            .borrow_mut()
            .insert((impl_def_id, law));
    }

    /// Records that the trait law `law` was checked at the trait arguments `trait_args`.
    pub fn instance_law_checked(&self, law: DefId, trait_args: mir_ty::GenericArgsRef<'tcx>) {
        self.instance_laws_checked
            .borrow_mut()
            .insert((law, self.tcx.erase_regions(trait_args)));
    }

    /// The uses of trait laws' contracts recorded so far, as (law, arguments).
    pub fn law_uses(&self) -> Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        self.law_uses.borrow().clone()
    }

    /// Whether a predicate the refinements of `rty` apply is derived, directly or through a
    /// definition, or not defined yet.
    pub fn may_apply_derived<FV>(&self, rty: &rty::RefinedType<FV>) -> bool {
        let system = self.system.borrow();
        let mut found = false;
        rty.any_pred(&mut |pred| {
            if let chc::Pred::UserDefined(p) = pred {
                found |= system.reaches_derived(p);
            }
            found
        });
        found
    }

    /// Stops if a derived predicate, or a predicate whose definition depends on one, appears in a
    /// contract Thrust does not check against a body; see [`derived_pred`].
    pub fn check_derived_predicates(&self) {
        derived_pred::check_law_uses(
            self.tcx,
            &self.per_instance_law_impls,
            &self.law_uses.borrow(),
            &self.instance_laws_checked.borrow(),
        );
        let derived = self.derived_preds.borrow();
        if derived.is_empty() {
            return;
        }
        derived_pred::check(
            self.tcx,
            &derived,
            &self.body_checks,
            &self.trait_laws.borrow(),
            &self.inherited_laws_checked.borrow(),
            &self.per_instance_law_impls,
            [
                self.def_ids.closure_precondition(),
                self.def_ids.closure_postcondition(),
                self.def_ids.closure_hist_inv(),
            ],
        );
    }

    pub fn impl_methods_with_own_contract(&self) -> Vec<DefId> {
        self.impl_methods_with_own_contract
            .iter()
            .copied()
            .collect()
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
            let defining = self.defining_predicates.borrow();
            if defining.contains(&key) && defining.last() != Some(&key) {
                self.tcx.dcx().span_fatal(
                    self.tcx.def_span(def_id),
                    "a predicate or logic function is called from a function or variant it calls, which is not supported",
                );
            }
            return pred.clone();
        }
        let pred = chc::UserDefinedPred::new(format!(
            "{}_{}",
            refine::user_defined_pred(self.tcx, def_id),
            self.predicate_instances.borrow().len(),
        ))
        .named(self.tcx.def_path_str(def_id));
        self.predicate_instances
            .borrow_mut()
            .insert(key, pred.clone());

        self.defining_predicates.borrow_mut().push(key);
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
        let arg_sorts: IndexVec<chc::TermVarIdx, chc::Sort> = formula_fn
            .params()
            .iter()
            .map(|ty| type_builder.build(*ty).to_sort())
            .collect();
        match formula_fn.body() {
            annot_fn::FormulaFnBody::Formula(formula) => {
                self.system.borrow_mut().push_pred_define_formula(
                    pred.clone(),
                    arg_sorts,
                    formula
                        .clone()
                        .map_var(|idx| chc::TermVarIdx::from(idx.index())),
                )
            }
            annot_fn::FormulaFnBody::Term(term) => {
                let term = term
                    .clone()
                    .map_var(|idx| chc::TermVarIdx::from(idx.index()));
                let (termination, decreases) = self.termination_clauses(
                    local_def_id,
                    generic_args,
                    owner_fn_id,
                    &pred,
                    &arg_sorts,
                    &term,
                );
                let mut system = self.system.borrow_mut();
                for clause in termination {
                    system.push_clause(clause);
                }
                system.push_fn_define_term(
                    pred.clone(),
                    arg_sorts,
                    type_builder.build(formula_fn.ret()).to_sort(),
                    term,
                    decreases,
                );
            }
        }
        self.defining_predicates.borrow_mut().pop();
        pred
    }

    /// The clauses requiring the variant of the logic function `local_def_id` to be
    /// non-negative and to decrease at each call `body` makes to `pred`, its own instance, under
    /// the conditions on the way to the call, and the variant if there is such a call. A `define-fun-rec` that does not terminate could
    /// make the query inconsistent, so the variant is translated while the function is being
    /// defined: a variant that calls it could otherwise be discharged by that inconsistency.
    fn termination_clauses(
        &self,
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
        pred: &chc::UserDefinedPred,
        arg_sorts: &IndexVec<chc::TermVarIdx, chc::Sort>,
        body: &chc::Term,
    ) -> (Vec<chc::Clause>, Option<chc::Term>) {
        let calls = body.guarded_calls(pred);
        if calls.is_empty() {
            return (Vec::new(), None);
        }
        let variant_def_id = self
            .extract_path_with_attr(local_def_id, &analyze::annot::variant_path_path())
            .expect("a recursive logic function has a variant");
        use mir_ty::TypeVisitableExt as _;
        self.defining_predicates.borrow_mut().push((
            variant_def_id,
            generic_args,
            generic_args.has_param().then_some(owner_fn_id),
        ));
        let variant_fn = self
            .formula_fn_with_args(variant_def_id.expect_local(), generic_args, owner_fn_id)
            .expect("a variant is a formula function");
        self.defining_predicates.borrow_mut().pop();
        let annot_fn::FormulaFnBody::Term(variant) = variant_fn.body() else {
            panic!("a variant is a term");
        };
        let variant = variant
            .clone()
            .map_var(|idx| chc::TermVarIdx::from(idx.index()));
        let name = self.tcx.def_path_str(local_def_id.to_def_id());

        let clauses = calls
            .into_iter()
            .flat_map(|call| {
                let mut builder = chc::ClauseBuilder::default();
                for (var, sort) in arg_sorts.iter_enumerated() {
                    builder.add_var(sort.clone());
                    builder.add_environment_origin(chc::debug::origin::Entry::parameter(var, sort));
                }
                for guard in call.guards {
                    builder.add_body(
                        guard.equal_to(chc::Term::bool(true)).into(),
                        chc::debug::origin::Entry::described(format!(
                            "a condition on the way to a recursive call of {name}"
                        )),
                    );
                }
                let at_call = variant.clone().subst_var(|v| call.args[v.index()].clone());
                let non_negative = chc::Atom::new(
                    chc::KnownPred::LESS_THAN_OR_EQUAL.into(),
                    vec![chc::Term::int(0), variant.clone()],
                );
                let smaller = chc::Atom::new(
                    chc::KnownPred::LESS_THAN.into(),
                    vec![at_call, variant.clone()],
                );
                let decreases = chc::Formula::Atom(non_negative).and(chc::Formula::Atom(smaller));
                builder.head(
                    decreases.into(),
                    chc::debug::origin::Entry::described(format!(
                        "the variant of {name} decreases at a recursive call"
                    )),
                )
            })
            .collect();
        (clauses, Some(variant))
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
        let fn_sig = self.tcx.fn_sig(def_id);
        let ret = if generic_args.is_empty() {
            fn_sig.skip_binder()
        } else {
            fn_sig.instantiate(self.tcx, generic_args)
        }
        .skip_binder()
        .output();
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

    pub fn def_ty_with_args(
        &mut self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> Option<rty::RefinedType> {
        self.def_ty_at(def_id, generic_args, caller_def_id, true)
    }

    /// The contract of `def_id` at `generic_args`, as [`Analyzer::def_ty_with_args`] gives it,
    /// without analyzing its body there: for a law whose proof the caller analyzes itself.
    pub fn contract_with_args(
        &mut self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> Option<rty::RefinedType> {
        self.def_ty_at(def_id, generic_args, caller_def_id, false)
    }

    fn def_ty_at(
        &mut self,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
        may_analyze: bool,
    ) -> Option<rty::RefinedType> {
        if !self.per_instance_law_impls.is_empty() && self.is_trait_law(def_id) {
            self.law_uses.borrow_mut().push((def_id, generic_args));
        }
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
        let analyze_body = may_analyze
            && deferred_ty_mode.is_some_and(|mode| mode.should_analyze())
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
                self.analyzed_instances
                    .borrow_mut()
                    .push((body_local_def_id.to_def_id(), generic_args));
            }
        }
        Some(expected)
    }

    /// Whether the body of `local_def_id` has been analyzed at type arguments that mention no
    /// type parameter, i.e. once per concrete instantiation reached from a call site.
    ///
    /// Every call at concrete type arguments re-analyzes the callee's body for those arguments
    /// (see [`Analyzer::def_ty_with_args`]), so such an instance checks the body against the
    /// contract instantiated at the call site, including the concrete closure contract of an
    /// `FnMut`-bounded type parameter.
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
                let reach =
                    self.pred_var_reach(&rty::RefinedType::<rty::Closed>::unrefined(fn_ty.into()));
                reach.found || reach.undefined
            })
        })
    }

    fn pred_var_reach<FV>(&self, rty: &rty::RefinedType<FV>) -> chc::PredVarReach {
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
        let config = crate::report::Config::from_env(self.tcx);
        match split_jobs() {
            Ok(None) => {}
            Ok(Some(jobs)) => {
                self.solve_parts(jobs, config.as_ref());
                return;
            }
            Err(err) => {
                self.tcx.dcx().err(err);
                return;
            }
        }
        let requests = config
            .as_ref()
            .map(crate::report::Config::requests)
            .unwrap_or_default();
        let answer = self.system.borrow().solve_with(requests);
        let refuted = match &config {
            Some(config) => {
                let system = self.system.borrow();
                self.report(config, &system, std::slice::from_ref(&answer), &[], &[])[0]
            }
            None => crate::report::Refuted::No,
        };
        let Err(err) = answer.result else {
            return;
        };
        let at = match refuted {
            crate::report::Refuted::AsError => return,
            crate::report::Refuted::At(span) => Some(span),
            crate::report::Refuted::No => None,
        };
        self.verification_error(&self.system.borrow(), &err, at)
            .emit();
    }

    /// The error of a failed verification of `system` (the whole or a part), at the obligation
    /// the report shows refuted, if it does.
    fn verification_error(
        &self,
        system: &chc::System,
        err: &chc::CheckSatError,
        refuted: Option<rustc_span::Span>,
    ) -> rustc_errors::Diag<'tcx> {
        let message = format!("verification error: {:?}", err);
        let mut diag = match refuted {
            Some(span) => self.tcx.dcx().struct_span_err(span, message),
            None => self.tcx.dcx().struct_err(message),
        };
        // `z3` reports what it cannot read as `(error …)` lines.
        let unread = matches!(err, chc::CheckSatError::Error { stdout, .. } if stdout.contains("(error "))
            && chc::Config::from_env().is_z3()
            && system.needs_pcsat();
        if unread {
            diag.help(
                "the query has forall sorts or sequences, which `z3` does not read; PCSat, the \
                 CHC solver of CoAR, does: set `THRUST_SOLVER` to the PCSat wrapper of Thrust \
                 (`tests/thrust-pcsat-wrapper` in its repository), which runs the CoAR image \
                 `COAR_IMAGE` in Docker",
            );
        }
        diag
    }

    /// Solves each part of the system that shares no unknown with the rest on its own
    /// (`THRUST_SPLIT`), reports the failing ones with the code their clauses come from and, with
    /// `report`, reports the parts as without `THRUST_SPLIT`.
    fn solve_parts(&self, jobs: usize, report: Option<&crate::report::Config>) {
        let system = self.system.borrow();
        let parts = system.solve_parts(jobs);
        let summaries: Vec<crate::report::Part> = parts
            .iter()
            .enumerate()
            .map(|(id, part)| crate::report::Part::new(self.tcx, &system, id, part))
            .collect();
        let refuted = match report {
            Some(config) => self.report_parts(config, jobs, &system, &parts, &summaries),
            None => vec![crate::report::Refuted::No; parts.len()],
        };
        for ((part, summary), refuted) in parts.iter().zip(&summaries).zip(refuted) {
            let Err(err) = &part.result else {
                continue;
            };
            let refuted = match refuted {
                crate::report::Refuted::AsError => continue,
                crate::report::Refuted::At(span) => Some(span),
                crate::report::Refuted::No => None,
            };
            // Without a refutation, the error is at the code of the part: its first function,
            // the others labelled.
            let code = summary.functions.first().map(|f| f.head);
            let mut diag =
                self.verification_error(&system.part(&part.clauses), err, refuted.or(code));
            if refuted.is_none() {
                for f in summary.functions.iter().skip(1) {
                    diag.span_label(f.head, format!("`{}` is in this part too", f.r#fn));
                }
            }
            diag.with_note(summary.error_note(self.tcx, &summaries))
                .emit();
        }
        crate::report::emit_part_notes(self.tcx, &summaries);
    }

    /// Reports the parts refuted, as without `THRUST_SPLIT`: each is solved once more on its own,
    /// asked for what the report needs. Returns how the report shows the refutation of each part.
    fn report_parts(
        &self,
        config: &crate::report::Config,
        jobs: usize,
        system: &chc::System,
        parts: &[chc::Part],
        summaries: &[crate::report::Part],
    ) -> Vec<crate::report::Refuted> {
        // Each part refuted is solved once more on its own, for its refutation, and each part
        // solved for its model when the report shows its unknowns; the report reads them over the
        // whole system, whose parts keep the clause ids. A solver that gives neither is not
        // asked again.
        let requests = config.requests();
        let solver = chc::Config::from_env();
        let evidence = solver.answers(requests);
        let shown = |part: &chc::Part| {
            let defs = system
                .pred_vars_of(&part.clauses)
                .into_iter()
                .filter_map(|p| self.template_sites.get(&p).map(|site| site.def()));
            defs.into_iter().any(|def| config.reports(self.tcx, def))
        };
        let asked: Vec<crate::report::Asked> = parts
            .iter()
            .enumerate()
            .filter_map(|(i, part)| {
                let refuted = match part.result {
                    Ok(()) if requests.model && evidence && shown(part) => false,
                    Err(chc::CheckSatError::Unsat) if requests.proof => true,
                    _ => return None,
                };
                Some(crate::report::Asked {
                    part: i + 1,
                    clauses: part.clauses.clone(),
                    refuted,
                })
            })
            .collect();
        // A refuted part of a solver that gives no refutation is refuted by `z3` when it reads it.
        let mut answers = chc::in_parallel(jobs, asked.len(), |i| {
            let part = system.part(&asked[i].clauses);
            if evidence {
                return part.solve_part_with(&solver, requests);
            }
            let mut answer = chc::Answer::of(Err(chc::CheckSatError::Unsat));
            if solver.asks_z3_to_refute(requests) {
                part.refute_by_z3(&mut answer);
            }
            answer
        });
        if answers.is_empty() {
            answers.push(chc::Answer::of(Ok(())));
        }
        // The templates and constraints of every part are shown, solved again or not.
        let spans = self.report(config, system, &answers, &asked, summaries);
        let mut refuted = vec![crate::report::Refuted::No; parts.len()];
        for (a, span) in asked.iter().zip(spans) {
            refuted[a.part - 1] = span;
        }
        refuted
    }

    fn report(
        &self,
        config: &crate::report::Config,
        system: &chc::System,
        answers: &[chc::Answer],
        asked: &[crate::report::Asked],
        parts: &[crate::report::Part],
    ) -> Vec<crate::report::Refuted> {
        let contracts = self
            .defs
            .iter()
            .filter_map(|(def_id, def_ty)| {
                let rty = match def_ty {
                    DefTy::Concrete(rty) => rty,
                    DefTy::Generic(generic) => generic.rty.as_ref()?,
                    DefTy::Deferred(_) => return None,
                };
                Some((def_id.as_local()?, rty.ty.as_function()?))
            })
            .collect();
        let blocks = self
            .basic_blocks
            .iter()
            .flat_map(|(key, blocks)| {
                blocks
                    .iter()
                    .map(move |(bb, def)| (key.local_def_id, *bb, &def.ty))
            })
            .collect();
        let body_checks = self.body_checks.snapshot();
        let input = crate::report::Input {
            system,
            contracts,
            blocks,
            answers,
            asked,
            template_sites: &self.template_sites,
            template_vars: &self.template_vars,
            contract_annotations: &self.contract_annotations,
            invariant_annotations: &self.invariant_annotations,
            body_checks: &body_checks,
            parts,
        };
        crate::report::emit(self.tcx, config, &input)
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
    ) -> Option<(DefId, chc::Formula<rty::FunctionParamIdx>)> {
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
        Some((formula_def_id.to_def_id(), formula_fn.to_require_formula()))
    }

    fn extract_ensure_annot(
        &self,
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<(
        DefId,
        chc::Formula<rty::RefinedTypeVar<rty::FunctionParamIdx>>,
    )> {
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
        Some((formula_def_id.to_def_id(), formula_fn.to_ensure_formula()))
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

    /// The clauses of the formula function `def_id` as written, read off the tail of its body
    /// (the macros conjoin the clauses of an annotation into one); the function where it has no
    /// tail.
    fn written_spans(&self, def_id: DefId) -> Vec<rustc_span::Span> {
        let body = def_id
            .as_local()
            .and_then(|def| self.tcx.hir_maybe_body_owned_by(def));
        let tail = body.and_then(|body| match body.value.kind {
            rustc_hir::ExprKind::Block(block, _) => block.expr,
            _ => None,
        });
        match tail {
            Some(tail) => written_clauses(tail),
            None => vec![self.tcx.def_span(def_id)],
        }
    }

    /// See [`BodyChecks`].
    pub fn body_checks(&self) -> BodyChecks {
        self.body_checks.clone()
    }

    /// Keeps where the written invariant of the loop at `header` of `def` is annotated, from the
    /// formula functions of its `invariant!`s.
    pub fn record_invariant_annotations(
        &mut self,
        def: LocalDefId,
        header: BasicBlock,
        formulas: impl Iterator<Item = LocalDefId>,
    ) {
        let spans = formulas
            .flat_map(|f| self.written_spans(f.to_def_id()))
            .collect();
        self.invariant_annotations.insert((def, header), spans);
    }

    /// Where a contract is annotated, from the companions it is read from: `requires`,
    /// `ensures`, and each refinement at its position.
    pub fn contract_annotations(
        &self,
        requires: Option<DefId>,
        ensures: Option<DefId>,
        refinements: impl Iterator<Item = (rty::TypePosition, DefId)>,
    ) -> ContractAnnotations {
        let spans = |def_id: DefId| self.written_spans(def_id);
        let mut annotations = ContractAnnotations {
            requires: requires.into_iter().flat_map(spans).collect(),
            ensures: ensures.into_iter().flat_map(spans).collect(),
            params: BTreeMap::new(),
        };
        for (position, def_id) in refinements {
            match position.steps().first() {
                Some(rty::TypePositionStep::Return) => annotations.ensures.extend(spans(def_id)),
                Some(rty::TypePositionStep::Param(idx)) => {
                    annotations.requires.extend(spans(def_id));
                    let param = annotations.params.entry(*idx).or_default();
                    param.extend(spans(def_id));
                }
                _ => annotations.requires.extend(spans(def_id)),
            }
        }
        annotations
    }

    /// Keeps where the written contract of `def_id` is annotated, for the report.
    pub fn record_contract_annotations(&mut self, def_id: DefId, annotations: ContractAnnotations) {
        if annotations.requires.is_empty() && annotations.ensures.is_empty() {
            return;
        }
        self.contract_annotations.insert(def_id, annotations);
    }

    /// Resolves every `#[thrust::refinement_path(..)]` annotation into a
    /// positioned refinement, by translating the referenced formula function, which it returns
    /// too.
    pub fn extract_refinement_annots(
        &self,
        local_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Vec<(
        rty::TypePosition,
        DefId,
        rty::Refinement<rty::FunctionParamIdx>,
    )> {
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
            out.push((position, def_id, formula_fn.to_refinement()));
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
