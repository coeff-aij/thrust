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

use rustc_middle::mir::MentionedItem;
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
    is_sought: T,
    /// How many times each def is on the path being followed; polymorphic recursion grows it.
    on_path: HashMap<DefId, usize>,
    reached: Vec<ReachedInstance<'tcx>>,
}

impl<'tcx> Analyzer<'tcx> {
    /// The instances of the defs `is_sought` holds of that the body analyses recorded since the
    /// last call can run, at the arguments each runs them at.
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
    pub fn instances_reached_from_new_analyses(
        &self,
        walk: &mut InstanceWalk<'tcx>,
        crate_mode: impl Fn(DefId) -> Option<Mode>,
        is_sought: impl Fn(DefId) -> bool,
    ) -> Vec<ReachedInstance<'tcx>> {
        let new_analyses: Vec<AnalysisKey<'tcx>> =
            self.analyzed_bodies.borrow()[walk.walked_analyses..].to_vec();
        walk.walked_analyses += new_analyses.len();
        let mut walker = Walker {
            analyzer: self,
            walk,
            crate_mode,
            is_sought,
            on_path: HashMap::new(),
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
        if matches!(instance.def, mir_ty::InstanceKind::Item(_)) && (self.is_sought)(def_id) {
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
        *self.on_path.get_mut(&def_id).unwrap() -= 1;
    }

    /// The instances `instance`'s body mentions, at its arguments.
    fn callees(
        &self,
        instance: mir_ty::Instance<'tcx>,
        env_def_id: DefId,
    ) -> Vec<mir_ty::Instance<'tcx>> {
        let tcx = self.tcx();
        let typing_env = mir_ty::TypingEnv::post_analysis(tcx, env_def_id);
        let body = tcx.instance_mir(instance.def);
        let mut callees = Vec::new();
        for item in body.mentioned_items() {
            let instantiate = |ty: Ty<'tcx>| {
                instance
                    .try_instantiate_mir_and_normalize_erasing_regions(
                        tcx,
                        typing_env,
                        mir_ty::EarlyBinder::bind(ty),
                    )
                    .unwrap_or_else(|_| {
                        tcx.dcx().span_fatal(
                            item.span,
                            format!(
                                "Thrust cannot normalize the type `{ty}` that `{instance}` uses, \
                                 so it cannot list the functions the body runs there"
                            ),
                        )
                    })
            };
            match item.node {
                MentionedItem::Fn(ty) => {
                    if let mir_ty::FnDef(def_id, args) = *instantiate(ty).kind() {
                        callees.extend(self.resolve(def_id, args, typing_env));
                    }
                }
                MentionedItem::Drop(ty) => {
                    self.drop_glue_callees(instantiate(ty), typing_env, &mut callees);
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
                    self.vtable_callees(source, target, typing_env, &mut callees);
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
        callees
    }

    /// The instance a call of `def_id` at `args` runs, if the arguments fix it.
    fn resolve(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        typing_env: mir_ty::TypingEnv<'tcx>,
    ) -> Option<mir_ty::Instance<'tcx>> {
        mir_ty::Instance::try_resolve(self.tcx(), typing_env, def_id, args)
            .ok()
            .flatten()
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
        let tcx = self.tcx();
        let mir_ty::Dynamic(predicates, ..) = *target.kind() else {
            return;
        };
        if source.is_trait() {
            return;
        }
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
