//! The instances of crate functions that the bodies a run analyzes can run, found with rustc's
//! `mentioned_items` (the edges of the monomorphization collector, kept in the MIR of every body,
//! std's included).
//!
//! A function whose body is checked only at the instances calls reach is checked, at an instance
//! the selection's code makes, only by an analysis of the body there. The analysis reaches the
//! instances its bodies call directly; this walk finds the others: those made inside a std body
//! (an `Option::map` of a function item), behind a trait method resolved at the instance, in
//! drop glue, through a vtable or a function pointer.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::interpret::{AllocId, GlobalAlloc, Scalar};
use rustc_middle::mir::visit::Visitor as _;
use rustc_middle::mir::{self, MentionedItem};
use rustc_middle::ty::{self as mir_ty, Ty, TyCtxt};
use rustc_span::def_id::DefId;

use crate::analyze::{self, AnalysisKey, Analyzer, Mode};

/// What the walk has done so far in a run, so that each call follows only what is new.
#[derive(Default)]
pub struct InstanceWalk<'tcx> {
    /// How many of the body analyses [`Analyzer::analyzed_bodies`] records have been walked from.
    walked_analyses: usize,
    /// The instances followed, each with the def in whose typing environment its arguments live.
    followed: HashSet<(mir_ty::Instance<'tcx>, DefId)>,
    /// The constant, promoted and static bodies walked, at their arguments.
    walked_constants: HashSet<(DefId, mir_ty::GenericArgsRef<'tcx>, Option<mir::Promoted>)>,
    /// The allocations of constant values walked.
    walked_allocs: HashSet<AllocId>,
}

/// An instance of a def the walk looks for, with the def in whose typing environment its
/// arguments live: the function a call there would be made from.
#[derive(Debug, Clone, Copy)]
pub struct ReachedInstance<'tcx> {
    pub def_id: DefId,
    pub generic_args: mir_ty::GenericArgsRef<'tcx>,
    pub env_def_id: DefId,
}

struct Walker<'a, 'tcx, M, T> {
    analyzer: &'a Analyzer<'tcx>,
    walk: &'a mut InstanceWalk<'tcx>,
    crate_mode: M,
    is_checked_per_instance: T,
    /// How many times each def is on the path being followed; polymorphic recursion grows it.
    on_path: HashMap<DefId, usize>,
    /// The instances on the path being followed, for the error messages.
    route: Vec<mir_ty::Instance<'tcx>>,
    reached: Vec<ReachedInstance<'tcx>>,
}

impl<'tcx> Analyzer<'tcx> {
    /// The instances of the defs `is_checked_per_instance` holds of that the body analyses
    /// recorded since the last call can run, at the arguments each runs them at.
    ///
    /// From each analyzed body at the arguments it was analyzed at, the calls, drop glue,
    /// vtables, function pointers and closures it mentions (rustc's `MentionedItem`s, which the
    /// monomorphization collector follows) are instantiated there and resolved in that analysis's
    /// typing environment (`Instance::try_resolve`), and followed transitively, into std bodies
    /// too. A call that resolves only once a type parameter is fixed is followed from the
    /// analysis that fixes it. Each instance is followed in a mode, as in
    /// [`Analyzer::stop_ignored_reached`]: a crate function's (`crate_mode`), or that of the
    /// path. Only verified code is followed: what a trusted body runs is its author's
    /// responsibility, but a generic trusted instance that verified code runs is verified code
    /// at that instance, as there.
    ///
    /// What `mentioned_items` leaves out is followed too: the constants a body names (promoted,
    /// unevaluated, and evaluated ones, through the functions, vtables and statics their values
    /// point to) and the statics it reads. In a promoted, constant or static body every function
    /// item and closure type is taken as run, whether or not the code calls it. Where the walk
    /// cannot tell an instance, it stops with an error rather than leaving it unchecked.
    pub fn instances_reached_from_new_analyses(
        &self,
        walk: &mut InstanceWalk<'tcx>,
        crate_mode: impl Fn(DefId) -> Option<Mode>,
        is_checked_per_instance: impl Fn(DefId) -> bool,
    ) -> Vec<ReachedInstance<'tcx>> {
        let new_analyses: Vec<AnalysisKey<'tcx>> =
            self.analyzed_bodies.borrow()[walk.walked_analyses..].to_vec();
        walk.walked_analyses += new_analyses.len();
        let mut walker = Walker {
            analyzer: self,
            walk,
            crate_mode,
            is_checked_per_instance,
            on_path: HashMap::new(),
            route: Vec::new(),
            reached: Vec::new(),
        };
        for key in new_analyses {
            let def_id = key.local_def_id().to_def_id();
            let args = analyze::body_args(self.tcx, def_id, key.generic_args());
            walker.follow(
                mir_ty::Instance::new_raw(def_id, args),
                key.env_def_id(self.tcx),
            );
        }
        walker.reached
    }
}

impl<'tcx, M, T> Walker<'_, 'tcx, M, T>
where
    M: Fn(DefId) -> Option<Mode>,
    T: Fn(DefId) -> bool,
{
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.analyzer.tcx
    }

    fn follow(&mut self, instance: mir_ty::Instance<'tcx>, env_def_id: DefId) {
        if !self.walk.followed.insert((instance, env_def_id)) {
            return;
        }
        let def_id = instance.def_id();
        if matches!(instance.def, mir_ty::InstanceKind::Item(_))
            && (self.is_checked_per_instance)(def_id)
        {
            self.reached.push(ReachedInstance {
                def_id,
                generic_args: instance.args,
                env_def_id,
            });
        }
        if !self.analyzer.runs_body(instance) {
            return;
        }
        let depth = self.on_path.entry(def_id).or_default();
        *depth += 1;
        if *depth > self.tcx().recursion_limit().0 {
            self.tcx().dcx().fatal(format!(
                "`{}` runs itself at ever larger type arguments, as a polymorphically recursive \
                 function does; Thrust cannot list the instances it runs",
                self.tcx().def_path_str(def_id),
            ));
        }
        self.route.push(instance);
        for callee in self.callees(instance, env_def_id) {
            let mode = match (self.crate_mode)(callee.def_id()) {
                Some(Mode::Trusted) if self.analyzer.is_generic(callee) => Mode::Verified,
                Some(mode) => mode,
                None => Mode::Verified,
            };
            if mode == Mode::Trusted {
                continue;
            }
            rustc_data_structures::stack::ensure_sufficient_stack(|| {
                self.follow(callee, env_def_id)
            });
        }
        self.route.pop();
        *self.on_path.get_mut(&def_id).unwrap() -= 1;
    }

    /// Stops: the walk cannot tell which instance `what` is, so a function checked only per
    /// instance that it may run would be checked nowhere.
    fn stop_undetermined(&self, what: String) -> ! {
        let route: Vec<String> = self
            .route
            .iter()
            .map(|instance| instance.to_string())
            .collect();
        self.tcx().dcx().fatal(format!(
            "Thrust cannot tell which instance {what} is, so a function whose body is checked only \
             at its instances may run unchecked there (reached through {})",
            route.join(" -> "),
        ))
    }

    /// The instances `instance`'s body mentions, at its arguments.
    fn callees(
        &mut self,
        instance: mir_ty::Instance<'tcx>,
        env_def_id: DefId,
    ) -> Vec<mir_ty::Instance<'tcx>> {
        let tcx = self.tcx();
        let typing_env = mir_ty::TypingEnv::post_analysis(tcx, env_def_id);
        let body = tcx.instance_mir(instance.def);
        let mut callees = Vec::new();
        for item in body.mentioned_items() {
            self.mentioned_callees(item.node, item.span, instance, typing_env, &mut callees);
        }
        self.constant_callees(body, instance, typing_env, &mut callees);
        callees
    }

    /// Instantiates `value`, a part of the body of `instance`, at its arguments.
    fn instantiate<V: mir_ty::TypeFoldable<TyCtxt<'tcx>> + std::fmt::Display + Copy>(
        &self,
        instance: mir_ty::Instance<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        value: V,
        span: rustc_span::Span,
    ) -> V {
        let tcx = self.tcx();
        instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                tcx,
                typing_env,
                mir_ty::EarlyBinder::bind(value),
            )
            .unwrap_or_else(|_| {
                tcx.dcx().span_fatal(
                    span,
                    format!(
                        "Thrust cannot normalize `{value}` that `{instance}` uses, so it cannot \
                         list the functions the body runs there"
                    ),
                )
            })
    }

    /// The instances a `MentionedItem` of the body of `instance` stands for, at its arguments.
    fn mentioned_callees(
        &self,
        item: MentionedItem<'tcx>,
        span: rustc_span::Span,
        instance: mir_ty::Instance<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        let tcx = self.tcx();
        let instantiate = |ty: Ty<'tcx>| self.instantiate(instance, typing_env, ty, span);
        {
            match item {
                MentionedItem::Fn(ty) => {
                    if let mir_ty::FnDef(def_id, args) = *instantiate(ty).kind() {
                        callees.extend(self.resolve(def_id, args, typing_env));
                    }
                }
                MentionedItem::Drop(ty) => {
                    self.drop_glue_callees(instantiate(ty), typing_env, callees);
                }
                MentionedItem::UnsizeCast {
                    source_ty,
                    target_ty,
                } => {
                    let (source, target) = self.unsized_tails(
                        instantiate(source_ty),
                        instantiate(target_ty),
                        typing_env,
                    );
                    self.vtable_callees(source, target, typing_env, callees);
                }
                MentionedItem::Closure(ty) => {
                    if let mir_ty::Closure(def_id, args) = *instantiate(ty).kind() {
                        callees.push(mir_ty::Instance::resolve_closure(
                            tcx,
                            def_id,
                            args,
                            mir_ty::ClosureKind::FnOnce,
                        ));
                    }
                }
            }
        }
    }

    /// The instance a call of `def_id` at `args` runs, if the arguments fix it. They do not when
    /// the call dispatches on a type parameter of the analysis the walk started from: the
    /// instance is then resolved at each concrete instantiation of that function, which the walk
    /// follows from the analysis that makes it, in this run or the run that selects its caller.
    /// A call that does not resolve at arguments without type parameters stops.
    fn resolve(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
    ) -> Option<mir_ty::Instance<'tcx>> {
        use mir_ty::TypeVisitableExt as _;
        match mir_ty::Instance::try_resolve(self.tcx(), typing_env, def_id, args) {
            Ok(Some(instance)) => Some(instance),
            Ok(None) if args.has_param() => None,
            Ok(None) | Err(_) => self.stop_undetermined(format!(
                "the call of `{}`",
                self.tcx().def_path_str_with_args(def_id, args)
            )),
        }
    }

    /// The instances the constants and statics the body of `instance` names run, and every
    /// function item and closure in the promoted and constant bodies they lead to.
    fn constant_callees(
        &mut self,
        body: &mir::Body<'tcx>,
        instance: mir_ty::Instance<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        let mut found = BodyConstants::default();
        found.visit_body(body);
        for (constant, span) in found.constants {
            let constant = self.instantiate(instance, typing_env, constant, span);
            self.const_callees(constant, instance, typing_env, callees);
        }
        for static_def_id in found.statics {
            self.static_callees(static_def_id, typing_env, callees);
        }
    }

    fn const_callees(
        &mut self,
        constant: mir::Const<'tcx>,
        instance: mir_ty::Instance<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        match constant {
            mir::Const::Ty(ty, ty_const) => match ty_const.kind() {
                mir_ty::ConstKind::Unevaluated(uv) => {
                    self.unevaluated_callees(uv.def, uv.args, None, ty, typing_env, callees);
                }
                // A value tree holds no pointer, and a parameter is fixed where the function is
                // instantiated.
                mir_ty::ConstKind::Value(_)
                | mir_ty::ConstKind::Param(_)
                | mir_ty::ConstKind::Infer(_)
                | mir_ty::ConstKind::Bound(..)
                | mir_ty::ConstKind::Placeholder(_)
                | mir_ty::ConstKind::Error(_)
                | mir_ty::ConstKind::Expr(_) => {}
            },
            mir::Const::Unevaluated(uv, ty) => {
                // A promoted's arguments are those of the body it is promoted from.
                let args = if uv.promoted.is_some() {
                    instance.args
                } else {
                    uv.args
                };
                self.unevaluated_callees(uv.def, args, uv.promoted, ty, typing_env, callees);
            }
            mir::Const::Val(value, _) => self.const_value_callees(value, typing_env, callees),
        }
    }

    /// What an unevaluated constant, or a promoted one, can run: every function item and closure
    /// in its body, which is walked as the rest of the walk's bodies are.
    fn unevaluated_callees(
        &mut self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        promoted: Option<mir::Promoted>,
        ty: Ty<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        use mir_ty::TypeVisitableExt as _;
        let tcx = self.tcx();
        let (instance, body) = if let Some(promoted) = promoted {
            let instance = mir_ty::Instance::new_raw(def_id, args);
            (instance, &tcx.promoted_mir(def_id)[promoted])
        } else {
            let instance = match mir_ty::Instance::try_resolve(tcx, typing_env, def_id, args) {
                Ok(Some(instance)) => instance,
                // An associated constant of a type parameter is resolved where the function is
                // instantiated, as a call is.
                Ok(None) if args.has_param() => return,
                Ok(None) | Err(_) => {
                    if !may_hold_code(ty) {
                        return;
                    }
                    self.stop_undetermined(format!(
                        "the constant `{}`",
                        tcx.def_path_str_with_args(def_id, args)
                    ))
                }
            };
            let const_def_id = instance.def_id();
            if !tcx.is_ctfe_mir_available(const_def_id) {
                if !may_hold_code(ty) {
                    return;
                }
                self.stop_undetermined(format!(
                    "the constant `{instance}`, whose body is not available,"
                ));
            }
            (instance, tcx.mir_for_ctfe(const_def_id))
        };
        if !self
            .walk
            .walked_constants
            .insert((instance.def_id(), instance.args, promoted))
        {
            return;
        }
        self.nested_body_callees(body, instance, typing_env, callees);
    }

    /// The instances a promoted, constant or static body holds: what its `MentionedItem`s would
    /// be, and every function item and closure its types name.
    fn nested_body_callees(
        &mut self,
        body: &mir::Body<'tcx>,
        instance: mir_ty::Instance<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        let mut mentions = NestedMentions {
            tcx: self.tcx(),
            body,
            items: Vec::new(),
        };
        mentions.visit_body(body);
        for local_decl in body.local_decls.iter() {
            mentions.code_in_type(local_decl.ty, local_decl.source_info.span);
        }
        for (item, span) in mentions.items {
            self.mentioned_callees(item, span, instance, typing_env, callees);
        }
        self.constant_callees(body, instance, typing_env, callees);
    }

    /// What a static's value can run: the functions, vtables and statics it points to.
    fn static_callees(
        &mut self,
        def_id: DefId,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        let tcx = self.tcx();
        if !self
            .walk
            .walked_constants
            .insert((def_id, mir_ty::List::empty(), None))
        {
            return;
        }
        let Ok(allocation) = tcx.eval_static_initializer(def_id) else {
            self.stop_undetermined(format!(
                "the value of the static `{}`, which Thrust cannot evaluate,",
                tcx.def_path_str(def_id)
            ));
        };
        for prov in allocation.inner().provenance().ptrs().values() {
            self.alloc_callees(prov.alloc_id(), typing_env, callees);
        }
    }

    fn const_value_callees(
        &mut self,
        value: mir::ConstValue,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        match value {
            mir::ConstValue::Scalar(Scalar::Ptr(ptr, _)) => {
                self.alloc_callees(ptr.provenance.alloc_id(), typing_env, callees);
            }
            mir::ConstValue::Indirect { alloc_id, .. }
            | mir::ConstValue::Slice { alloc_id, .. } => {
                self.alloc_callees(alloc_id, typing_env, callees);
            }
            mir::ConstValue::Scalar(Scalar::Int(_)) | mir::ConstValue::ZeroSized => {}
        }
    }

    /// What an allocation of a constant value points to, as the collector's `collect_alloc`
    /// follows it.
    fn alloc_callees(
        &mut self,
        alloc_id: AllocId,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        if !self.walk.walked_allocs.insert(alloc_id) {
            return;
        }
        let tcx = self.tcx();
        match tcx.global_alloc(alloc_id) {
            GlobalAlloc::Function { instance } => callees.push(instance),
            GlobalAlloc::VTable(ty, predicates) => {
                self.vtable_methods(ty, predicates, typing_env, callees);
            }
            GlobalAlloc::Static(def_id) => self.static_callees(def_id, typing_env, callees),
            GlobalAlloc::Memory(allocation) => {
                for prov in allocation.inner().provenance().ptrs().values() {
                    self.alloc_callees(prov.alloc_id(), typing_env, callees);
                }
            }
            GlobalAlloc::TypeId { .. } => {}
        }
    }

    /// The functions dropping a value of type `ty` runs: the `Drop` impl of each type in it, as
    /// the drop glue rustc builds runs them. A type parameter's are found where it is fixed.
    fn drop_glue_callees(
        &self,
        ty: Ty<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        let mut pending = vec![ty];
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) || !ty.needs_drop(self.tcx(), typing_env) {
                continue;
            }
            pending.extend(self.dropped_parts(ty, typing_env, callees));
        }
    }

    /// The parts of a value of type `ty` that dropping it drops, after pushing its own `Drop`
    /// impl to `callees`.
    fn dropped_parts(
        &self,
        ty: Ty<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) -> Vec<Ty<'tcx>> {
        let tcx = self.tcx();
        match *ty.kind() {
            mir_ty::Adt(adt, args) => {
                if adt.has_dtor(tcx) {
                    let drop_fn = tcx.associated_item_def_ids(
                        tcx.require_lang_item(rustc_hir::LangItem::Drop, rustc_span::DUMMY_SP),
                    )[0];
                    callees.extend(self.resolve(drop_fn, tcx.mk_args(&[ty.into()]), typing_env));
                }
                if let Some(boxed) = ty.boxed_ty() {
                    return vec![boxed];
                }
                if adt.is_manually_drop() {
                    return Vec::new();
                }
                adt.all_fields().map(|field| field.ty(tcx, args)).collect()
            }
            mir_ty::Tuple(tys) => tys.to_vec(),
            mir_ty::Array(elem, _) | mir_ty::Slice(elem) | mir_ty::Pat(elem, _) => vec![elem],
            mir_ty::Closure(_, args) => args.as_closure().upvar_tys().to_vec(),
            mir_ty::CoroutineClosure(_, args) => args.as_coroutine_closure().upvar_tys().to_vec(),
            // A trait object's drop glue is in its vtable, listed where it is made.
            mir_ty::Dynamic(..) => Vec::new(),
            mir_ty::Coroutine(..) => tcx.dcx().fatal(format!(
                "Thrust cannot list the functions dropping the coroutine `{ty}` runs"
            )),
            mir_ty::Bool
            | mir_ty::Char
            | mir_ty::Int(_)
            | mir_ty::Uint(_)
            | mir_ty::Float(_)
            | mir_ty::Foreign(_)
            | mir_ty::Str
            | mir_ty::RawPtr(..)
            | mir_ty::Ref(..)
            | mir_ty::FnDef(..)
            | mir_ty::FnPtr(..)
            | mir_ty::UnsafeBinder(_)
            | mir_ty::CoroutineWitness(..)
            | mir_ty::Never
            | mir_ty::Alias(..)
            | mir_ty::Param(_)
            | mir_ty::Bound(..)
            | mir_ty::Placeholder(_)
            | mir_ty::Infer(_)
            | mir_ty::Error(_) => Vec::new(),
        }
    }

    /// The source and target types an unsizing coercion from `source` to `target` turns into a
    /// trait object or a slice, past the pointer or the smart pointer (`Box`, `Rc`, a
    /// `CoerceUnsized` struct) both are.
    fn unsized_tails(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
    ) -> (Ty<'tcx>, Ty<'tcx>) {
        let tcx = self.tcx();
        if let (Some(source_pointee), Some(target_pointee)) =
            (source.builtin_deref(true), target.builtin_deref(true))
        {
            return tcx.struct_lockstep_tails_for_codegen(
                source_pointee,
                target_pointee,
                typing_env,
            );
        }
        if let (Some(source_boxed), Some(target_boxed)) = (source.boxed_ty(), target.boxed_ty()) {
            return tcx.struct_lockstep_tails_for_codegen(source_boxed, target_boxed, typing_env);
        }
        let (mir_ty::Adt(adt, source_args), mir_ty::Adt(_, target_args)) =
            (*source.kind(), *target.kind())
        else {
            return (source, target);
        };
        // A `CoerceUnsized` struct differs between the two in the one field it coerces.
        let coerced = adt.non_enum_variant().fields.iter().find_map(|field| {
            let source_field = field.ty(tcx, source_args);
            let target_field = field.ty(tcx, target_args);
            (source_field != target_field).then_some((source_field, target_field))
        });
        match coerced {
            Some((source_field, target_field)) => {
                let normalize = |ty| tcx.normalize_erasing_regions(typing_env, ty);
                self.unsized_tails(normalize(source_field), normalize(target_field), typing_env)
            }
            None => (source, target),
        }
    }

    /// The methods of the vtable an unsizing coercion from `source` to the trait object `target`
    /// makes, and the drop glue of `source` it holds.
    fn vtable_callees(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        let mir_ty::Dynamic(predicates, ..) = *target.kind() else {
            return;
        };
        if source.is_trait() {
            return;
        }
        self.vtable_methods(source, predicates, typing_env, callees);
    }

    /// The methods of the vtable of `source` as a trait object with `predicates`, and the drop
    /// glue of `source` it holds.
    fn vtable_methods(
        &self,
        source: Ty<'tcx>,
        predicates: &'tcx mir_ty::List<mir_ty::PolyExistentialPredicate<'tcx>>,
        typing_env: mir_ty::TypingEnv<'tcx>,
        callees: &mut Vec<mir_ty::Instance<'tcx>>,
    ) {
        let tcx = self.tcx();
        self.drop_glue_callees(source, typing_env, callees);
        let Some(principal) = predicates.principal() else {
            return;
        };
        let trait_ref =
            tcx.instantiate_bound_regions_with_erased(principal.with_self_ty(tcx, source));
        let supertraits = mir_ty::elaborate::supertraits(tcx, mir_ty::Binder::dummy(trait_ref))
            .collect::<Vec<_>>();
        for supertrait in supertraits {
            let supertrait = tcx.instantiate_bound_regions_with_erased(supertrait);
            for method in tcx.own_existential_vtable_entries(supertrait.def_id) {
                callees.extend(self.resolve(*method, supertrait.args, typing_env));
            }
        }
    }
}

/// Whether a value of type `ty` can hold code: a function, a closure, a trait object, or a type
/// not known here.
fn may_hold_code(ty: Ty<'_>) -> bool {
    ty.walk().any(|arg| {
        arg.as_type().is_some_and(|ty| {
            matches!(
                ty.kind(),
                mir_ty::FnDef(..)
                    | mir_ty::FnPtr(..)
                    | mir_ty::Closure(..)
                    | mir_ty::CoroutineClosure(..)
                    | mir_ty::Coroutine(..)
                    | mir_ty::Dynamic(..)
                    | mir_ty::Param(_)
                    | mir_ty::Alias(..)
            )
        })
    })
}

/// The constants a body names, and the statics it reads as thread-locals.
#[derive(Default)]
struct BodyConstants<'tcx> {
    constants: Vec<(mir::Const<'tcx>, rustc_span::Span)>,
    statics: Vec<DefId>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for BodyConstants<'tcx> {
    fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, location: mir::Location) {
        self.constants.push((constant.const_, constant.span));
        self.super_const_operand(constant, location);
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
        if let mir::Rvalue::ThreadLocalRef(def_id) = rvalue {
            self.statics.push(*def_id);
        }
        self.super_rvalue(rvalue, location);
    }
}

/// The `MentionedItem`s of a promoted, constant or static body, which rustc records only for
/// the bodies of functions: the sites `rustc_mir_transform`'s `MentionedItems` pass records, and
/// every function item and closure type the body names.
struct NestedMentions<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    items: Vec<(MentionedItem<'tcx>, rustc_span::Span)>,
}

impl<'tcx> NestedMentions<'_, 'tcx> {
    fn code_in_type(&mut self, ty: Ty<'tcx>, span: rustc_span::Span) {
        for arg in ty.walk() {
            let Some(ty) = arg.as_type() else {
                continue;
            };
            match ty.kind() {
                mir_ty::FnDef(..) => self.items.push((MentionedItem::Fn(ty), span)),
                mir_ty::Closure(..) => self.items.push((MentionedItem::Closure(ty), span)),
                _ => {}
            }
        }
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for NestedMentions<'_, 'tcx> {
    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: mir::Location) {
        let span = self.body.source_info(location).span;
        match &terminator.kind {
            mir::TerminatorKind::Call { func, .. } | mir::TerminatorKind::TailCall { func, .. } => {
                let ty = func.ty(self.body, self.tcx);
                self.items.push((MentionedItem::Fn(ty), span));
            }
            mir::TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(self.body, self.tcx).ty;
                self.items.push((MentionedItem::Drop(ty), span));
            }
            _ => {}
        }
        self.super_terminator(terminator, location);
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
        use rustc_middle::ty::adjustment::PointerCoercion;
        let span = self.body.source_info(location).span;
        if let mir::Rvalue::Cast(mir::CastKind::PointerCoercion(coercion, _), operand, target_ty) =
            rvalue
        {
            let source_ty = operand.ty(self.body, self.tcx);
            let item = match coercion {
                PointerCoercion::Unsize => Some(MentionedItem::UnsizeCast {
                    source_ty,
                    target_ty: *target_ty,
                }),
                PointerCoercion::ReifyFnPointer => Some(MentionedItem::Fn(source_ty)),
                PointerCoercion::ClosureFnPointer(_) => Some(MentionedItem::Closure(source_ty)),
                _ => None,
            };
            self.items.extend(item.map(|item| (item, span)));
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, location: mir::Location) {
        self.code_in_type(constant.ty(), constant.span);
        self.super_const_operand(constant, location);
    }
}
