//! Analyze a local crate.

use std::collections::HashSet;

use rustc_hir::def_id::CRATE_DEF_ID;
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::LocalDefId;

use crate::analyze;
use crate::analyze::selection::ItemPath;
use crate::chc;
use crate::chc::debug;
use crate::rty::ClauseBuilderExt as _;

/// An implementation of local crate analysis.
///
/// The entry point is [`Analyzer::run`], which performs the following steps in order:
///
/// 1. Register enum definitions found in the crate.
/// 2. Give initial refinement types to local function definitions based on their signatures and
///    annotations. This generates template refinement types with predicate variables for parameters and
///    return types that are not known via annotations.
/// 3. Type local function definition bodies via [`super::local_def::Analyzer`] using the refinement types
///    generated in the previous step.
pub struct Analyzer<'tcx, 'ctx> {
    tcx: TyCtxt<'tcx>,
    ctx: &'ctx mut analyze::Analyzer<'tcx>,

    skip_analysis: HashSet<LocalDefId>,
    selection: Option<analyze::selection::Selection>,
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    fn analyze_raw_command_annot(&mut self) {
        for attrs in self.tcx.get_attrs_by_path(
            CRATE_DEF_ID.to_def_id(),
            &analyze::annot::raw_command_path(),
        ) {
            use rustc_ast::token::{LitKind, Token, TokenKind};
            use rustc_ast::tokenstream::TokenTree;

            let ts = analyze::annot::extract_annot_tokens(attrs.clone());
            let tt = ts.iter().next().expect("string literal").clone();

            let raw_command = match tt {
                TokenTree::Token(
                    Token {
                        kind: TokenKind::Literal(lit),
                        ..
                    },
                    _,
                ) if lit.kind == LitKind::Str => lit.symbol.to_string(),
                _ => panic!("invalid raw_command annotation"),
            };

            self.ctx
                .system
                .borrow_mut()
                .push_raw_command(chc::RawCommand {
                    command: raw_command,
                });
        }
    }

    fn refine_local_defs(&mut self) {
        // Prioritize trait method specs so that they are always available when refining trait impl
        // functions; see the partialeq_impl.rs case.
        let mut keys = self.tcx.mir_keys(()).clone();
        // Refinement order decides how predicate variables are numbered, so collect these
        // in the order `mir_keys` yields them rather than in a hash order.
        let mut trait_method_spec_keys = Vec::new();
        let mut local_spec_targets = Vec::new();
        for local_def_id in self.tcx.mir_keys(()) {
            if !self.tcx.def_kind(*local_def_id).is_fn_like() {
                keys.swap_remove(local_def_id);
                continue;
            }
            let analyzer = self.ctx.local_def_analyzer(*local_def_id);
            if analyzer.is_annotated_as_extern_spec_fn() {
                let target_def_id = analyzer.extern_spec_fn_target_def_id();
                if let Some(local_target_def_id) = target_def_id.as_local() {
                    keys.swap_remove(&local_target_def_id);
                    local_spec_targets.push(local_target_def_id);
                    // The spec is the target's contract; a trusted target's body is not
                    // checked against it.
                    if self
                        .tcx
                        .get_attrs_by_path(target_def_id, &analyze::annot::trusted_path())
                        .next()
                        .is_some()
                    {
                        self.skip_analysis.insert(local_target_def_id);
                    }
                }
                if matches!(
                    self.tcx.def_kind(target_def_id),
                    rustc_hir::def::DefKind::AssocFn
                ) {
                    trait_method_spec_keys.push(*local_def_id);
                    keys.swap_remove(local_def_id);
                }
            }
            if analyzer.is_annotated_as_ignored() {
                self.skip_analysis.insert(*local_def_id);
                keys.swap_remove(local_def_id);
            }
            let is_predicate = analyzer.is_annotated_as_predicate();
            let is_formula_fn = analyzer.is_annotated_as_formula_fn();
            if is_predicate || is_formula_fn {
                if is_formula_fn {
                    self.ctx.register_formula_fn(*local_def_id);
                }
                if is_predicate && !is_formula_fn {
                    self.ctx
                        .local_def_analyzer(*local_def_id)
                        .analyze_predicate_definition();
                }
                self.skip_analysis.insert(*local_def_id);
                keys.swap_remove(local_def_id);
            }
        }
        // Nor is the body of a target outside `verify_only`, whose contract the spec writes.
        for local_target_def_id in local_spec_targets {
            if self.is_outside_selection(local_target_def_id) {
                self.skip_analysis.insert(local_target_def_id);
            }
        }
        // A closure is skipped when its typeck root is, so roots are refined first.
        let (roots, nested): (Vec<&LocalDefId>, Vec<&LocalDefId>) = keys
            .iter()
            .partition(|id| self.tcx.typeck_root_def_id(id.to_def_id()) == id.to_def_id());
        for local_def_id in &trait_method_spec_keys {
            self.refine_fn_def(*local_def_id);
        }
        for local_def_id in roots.into_iter().chain(nested) {
            self.refine_fn_def(*local_def_id);
        }
    }

    /// Whether `local_def_id` is a function outside the selection of `#![thrust::verify_only(..)]`
    /// whose body is trusted when its contract is written: a typeck root that is not a trait law.
    fn is_outside_selection(&self, local_def_id: LocalDefId) -> bool {
        let def_id = local_def_id.to_def_id();
        self.selection.as_ref().is_some_and(|selection| {
            self.tcx.typeck_root_def_id(def_id) == def_id
                && !self.is_trait_law(local_def_id)
                && !selection.contains(self.tcx, def_id)
        })
    }

    /// Reports each `#![thrust::verify_only(..)]` entry that selects no function of the crate,
    /// nor a law inherited by one of its impls.
    fn report_unmatched_selection(&self) {
        let Some(selection) = &self.selection else {
            return;
        };
        let mut paths: Vec<_> = self
            .tcx
            .mir_keys(())
            .iter()
            .map(|local_def_id| local_def_id.to_def_id())
            .filter(|def_id| self.tcx.def_kind(*def_id).is_fn_like())
            .map(|def_id| ItemPath::of(self.tcx, def_id))
            .collect();
        for (trait_def_id, laws) in self.ctx.trait_laws.borrow().iter() {
            let impls = self.tcx.all_local_trait_impls(()).get(trait_def_id);
            for impl_local in impls.into_iter().flatten() {
                for law_def_id in laws {
                    paths.push(ItemPath::of_inherited(
                        self.tcx,
                        impl_local.to_def_id(),
                        *law_def_id,
                    ));
                }
            }
        }
        selection.report_unmatched(self.tcx, &paths);
    }

    #[tracing::instrument(skip(self), fields(def_id = %self.tcx.def_path_str(local_def_id)))]
    fn refine_fn_def(&mut self, local_def_id: LocalDefId) {
        let sig = self.ctx.fn_sig(local_def_id.to_def_id());
        let outside_selection = self.is_outside_selection(local_def_id);
        let mut analyzer = self.ctx.local_def_analyzer(local_def_id);

        if analyzer.is_annotated_as_trusted() {
            assert!(
                analyzer.is_fully_annotated(),
                "`#[thrust::trusted]` needs both `requires` and `ensures` (or `#[thrust::callable]`) on `{}`",
                self.tcx.def_path_str(local_def_id)
            );
            self.skip_analysis.insert(local_def_id);
        }

        if analyzer.is_injected_std() {
            self.skip_analysis.insert(local_def_id);
        }

        if analyzer.is_annotated_as_extern_spec_fn() {
            assert!(
                analyzer.is_fully_annotated(),
                "an extern spec needs both `requires` and `ensures` (or `#[thrust::callable]`) on `{}`",
                self.tcx.def_path_str(local_def_id)
            );
            self.skip_analysis.insert(local_def_id);
        }

        // skip analysis if the def is closure defined in skipped def
        if let Some(root_local_def_id) = self
            .tcx
            .typeck_root_def_id(local_def_id.to_def_id())
            .as_local()
        {
            if root_local_def_id != local_def_id && self.skip_analysis.contains(&root_local_def_id)
            {
                self.skip_analysis.insert(local_def_id);
                return;
            }
        }

        // Outside `verify_only`, a function whose contract leaves nothing to infer from its body
        // is trusted, as `#[thrust::trusted]` is; one with a predicate variable in its contract
        // is analyzed, because its callers use the contract inferred from its body.
        let mut expected = None;
        if outside_selection && !self.skip_analysis.contains(&local_def_id) {
            let ty = analyzer.expected_ty();
            if !ty.has_pred_var() {
                tracing::debug!("trusted outside verify_only");
                self.skip_analysis.insert(local_def_id);
            }
            expected = Some(ty);
        }

        let owner_fn_id = analyzer.owner_fn_id;
        let owner_fn_id_args = analyzer.owner_fn_id_args;
        use mir_ty::TypeVisitableExt as _;
        if sig.has_param() {
            if owner_fn_id.as_local().is_none_or(|def_id| {
                self.skip_analysis.contains(&def_id) || !self.tcx.is_mir_available(def_id)
            }) {
                self.ctx.register_deferred_def_without_analysis(
                    owner_fn_id,
                    local_def_id,
                    owner_fn_id_args,
                );
            } else if per_instance_generics() {
                // Upstream Thrust's treatment: the body is analyzed at each instance a call site
                // reaches, and not once over the type parameters.
                self.ctx
                    .register_deferred_def(owner_fn_id, local_def_id, owner_fn_id_args);
            } else {
                let expected = expected.unwrap_or_else(|| analyzer.expected_ty());
                self.ctx
                    .register_generic_def(owner_fn_id, local_def_id, Some(expected));
            }
        } else {
            let expected = expected.unwrap_or_else(|| analyzer.expected_ty());
            self.ctx.register_def(owner_fn_id, expected);
        }
    }

    fn analyze_local_defs(&mut self) {
        // Inherited laws first: with them after the bodies, the `skip_take` query (the same clauses
        // in another order) is not answered by the solver within 300 s, where it answers in 8 s.
        self.analyze_inherited_laws();
        // A def with an `FnMut`-bounded type parameter is decided after every other body has
        // been analyzed, because the call sites that instantiate it are found by analyzing
        // those bodies.
        let mut fn_mut_generic_defs = Vec::new();
        for local_def_id in self.tcx.mir_keys(()) {
            if self.is_trait_law(*local_def_id) {
                // A law's default body over `Self` would be checked with the law itself among
                // the premises of `Self`'s predicates, which proves nothing; it is checked at
                // each impl instead (`analyze_inherited_laws`).
                continue;
            }
            if self.has_fn_mut_bounded_param(*local_def_id) {
                fn_mut_generic_defs.push(*local_def_id);
                continue;
            }
            self.analyze_placeholder(*local_def_id);
        }
        // A def is skipped (D34) when a concrete instantiation has analyzed its body and no
        // instance has used its generic analysis instead. Only a def whose specification relates
        // the closure's states by `hist_inv!` can have such an instance
        // (`Analyzer::reuse_fn_mut_generic`); analyzing a def may add one for a def skipped
        // before, which is then analyzed too.
        let mut pending = fn_mut_generic_defs;
        while !pending.is_empty() {
            let mut skipped = Vec::new();
            for local_def_id in pending {
                if self.ctx.has_concrete_instance(local_def_id)
                    && !self.ctx.has_reused_instance(local_def_id)
                {
                    // The placeholder analysis would check the body against a closure contract
                    // that is a free forall predicate, which no clause relates to the concrete
                    // closures of this crate. An `FnMut` closure's state changes between calls,
                    // so a body obligation relating the contract at two states (a preservation
                    // conjunct of an adapter invariant) need not be inductive for an arbitrary
                    // contract even when it is for every concrete one; creusot-std guards it
                    // by `hist_inv!` for that reason. Each concrete instantiation has checked the
                    // body against its own closure contract instead.
                    skipped.push(local_def_id);
                    continue;
                }
                self.analyze_placeholder(local_def_id);
            }
            pending = skipped
                .into_iter()
                .filter(|local_def_id| {
                    let reused = self.ctx.has_reused_instance(*local_def_id);
                    if !reused {
                        tracing::debug!(?local_def_id, "verified per concrete instantiation");
                    }
                    reused
                })
                .collect();
        }
    }

    /// Whether `local_def_id` is a `#[thrust::law]` declared in a local trait.
    fn is_trait_law(&self, local_def_id: LocalDefId) -> bool {
        let def_id = local_def_id.to_def_id();
        self.ctx
            .trait_laws
            .borrow()
            .values()
            .any(|laws| laws.contains(&def_id))
    }

    /// Checks, at every local impl of a trait with laws, each `#[thrust::law]` the impl does not
    /// define itself.
    ///
    /// A law is declared once in the trait with its contract and a default body (`{}` when the
    /// solver needs no proof steps), and each impl inherits it. This is the shape Creusot
    /// restates in each impl (`#[law]` with the trait's contract and an empty body); here the
    /// impl writes the law only when it needs proof steps. The trait's default body is analyzed
    /// with `Self` (and the trait's own arguments) set to the impl's, the impl's type parameters
    /// left as placeholders, against the law's contract at those arguments: the obligation an
    /// impl that writes the law with an empty body is checked against. Only local impls are
    /// checked.
    fn analyze_inherited_laws(&mut self) {
        let trait_laws = self.ctx.trait_laws.borrow().clone();
        for (trait_def_id, laws) in trait_laws {
            let impls: Vec<LocalDefId> = self
                .tcx
                .all_local_trait_impls(())
                .get(&trait_def_id)
                .cloned()
                .unwrap_or_default();
            for impl_local in impls {
                let impl_def_id = impl_local.to_def_id();
                let implemented = self.tcx.impl_item_implementor_ids(impl_def_id);
                let Some(owner) = self
                    .tcx
                    .associated_item_def_ids(impl_def_id)
                    .iter()
                    .copied()
                    .find(|id| self.tcx.def_kind(*id).is_fn_like())
                else {
                    continue;
                };
                let trait_ref = self
                    .tcx
                    .impl_trait_ref(impl_def_id)
                    .unwrap()
                    .instantiate_identity();
                let args = self.tcx.erase_regions(trait_ref.args);
                for law_def_id in &laws {
                    if implemented.contains_key(law_def_id) {
                        continue;
                    }
                    if self
                        .selection
                        .as_ref()
                        .is_some_and(|s| !s.contains_inherited(self.tcx, impl_def_id, *law_def_id))
                    {
                        tracing::info!(
                            ?law_def_id,
                            ?impl_def_id,
                            "inherited law assumed outside verify_only"
                        );
                        continue;
                    }
                    let Some(law_local) = law_def_id.as_local() else {
                        continue;
                    };
                    if !self.tcx.is_mir_available(*law_def_id) {
                        tracing::warn!(?law_def_id, ?impl_def_id, "inherited law has no body");
                        continue;
                    }
                    tracing::info!(
                        ?law_def_id,
                        ?impl_def_id,
                        ?args,
                        "inherited law checked at impl"
                    );
                    // A trait method with a default body carries its contract on the spec
                    // function the macro generates, so the contract is read as a call site
                    // reads it, at the impl's arguments.
                    let Some(expected) = self.ctx.def_ty_with_args(*law_def_id, args, owner) else {
                        tracing::warn!(?law_def_id, ?impl_def_id, "inherited law has no contract");
                        continue;
                    };
                    let mut analyzer = self.ctx.local_def_analyzer(law_local);
                    analyzer.owner_fn_id(owner).generic_args(args);
                    analyzer.run(&expected);
                }
            }
        }
    }

    /// Check a local def's body with its type parameters left as opaque types (a no-op
    /// substitution if the def is monomorphic).
    fn analyze_placeholder(&mut self, local_def_id: LocalDefId) {
        if !self.tcx.def_kind(local_def_id).is_fn_like() {
            return;
        };
        if self.skip_analysis.contains(&local_def_id) {
            tracing::debug!("this is marked as skip analysis: {:?}", local_def_id);
            return;
        }

        let Some(expected) = self.ctx.concrete_def_ty(local_def_id.to_def_id()) else {
            // when the local_def_id is deferred it would be skipped
            tracing::debug!("this is marked as deferred type: {:?}", local_def_id);
            return;
        };

        let expected = expected.clone();
        let generic_args = self.placeholder_generic_args(local_def_id);
        self.ctx
            .local_def_analyzer(local_def_id)
            .generic_args(generic_args)
            .run(&expected);
    }

    /// Whether a type parameter in scope of `local_def_id` (its own or an enclosing item's) is
    /// bounded by `FnMut`. `Fn` and `FnOnce` bounds do not count: their closure state does not
    /// change between calls, and such defs keep their generic verification.
    fn has_fn_mut_bounded_param(&self, local_def_id: LocalDefId) -> bool {
        self.tcx.def_kind(local_def_id).is_fn_like()
            && !analyze::fn_mut_bounded_params(self.tcx, local_def_id.to_def_id()).is_empty()
    }

    fn placeholder_generic_args(&self, local_def_id: LocalDefId) -> mir_ty::GenericArgsRef<'tcx> {
        let mut constrained_params = HashSet::new();
        let predicates = self.tcx.predicates_of(local_def_id);
        let sized_trait = self.tcx.lang_items().sized_trait().unwrap();
        for (clause, _) in predicates.predicates {
            let mir_ty::ClauseKind::Trait(pred) = clause.kind().skip_binder() else {
                continue;
            };
            if pred.def_id() == sized_trait {
                continue;
            };
            for arg in pred.trait_ref.args.iter().flat_map(|ty| ty.walk()) {
                let Some(ty) = arg.as_type() else {
                    continue;
                };
                let mir_ty::TyKind::Param(param_ty) = ty.kind() else {
                    continue;
                };
                constrained_params.insert(param_ty.index);
            }
        }

        let mut args: Vec<mir_ty::GenericArg<'tcx>> = Vec::new();

        let generics = self.tcx.generics_of(local_def_id);
        for idx in 0..generics.count() {
            let param = generics.param_at(idx, self.tcx);
            let arg = match param.kind {
                mir_ty::GenericParamDefKind::Type { .. } => {
                    let new_param = mir_ty::Ty::new_param(self.tcx, param.index, param.name).into();
                    tracing::debug!(
                        "replace the cosnstrained param {:#?} with the new param {:#?}.",
                        param,
                        new_param
                    );
                    new_param
                }
                mir_ty::GenericParamDefKind::Const { .. } => mir_ty::Const::new_param(
                    self.tcx,
                    mir_ty::ParamConst::new(param.index, param.name),
                )
                .into(),
                mir_ty::GenericParamDefKind::Lifetime => self.tcx.lifetimes.re_erased.into(),
            };
            args.push(arg);
        }

        self.tcx.mk_args(&args)
    }

    fn assert_callable_entry(&mut self) {
        if let Some((def_id, _)) = self.tcx.entry_fn(()) {
            // we want to assert entry function is safe to execute without any assumption
            // TODO: replace code here with relate_* in Env + Refine context (created with empty env)
            let entry_ty = self
                .ctx
                .concrete_def_ty(def_id)
                .unwrap()
                .ty
                .as_function()
                .unwrap()
                .clone();
            let mut builder = chc::ClauseBuilder::default();
            for (param_idx, param_ty) in entry_ty.params.iter_enumerated() {
                let param_sort = param_ty.ty.to_sort();
                if !param_sort.is_singleton() {
                    let chc_var = builder.add_mapped_var(param_idx, param_sort.clone());
                    builder.add_environment_origin(
                        debug::origin::Entry::parameter(param_idx, &param_sort)
                            .var_mapping(param_idx, chc_var),
                    );
                }
            }
            for param_ty in entry_ty.params {
                let cs = builder
                    .clone()
                    .with_value_var(&param_ty.ty)
                    .head(param_ty.refinement);
                self.ctx.extend_clauses(cs);
            }
        }
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    pub fn new(ctx: &'ctx mut analyze::Analyzer<'tcx>) -> Self {
        let tcx = ctx.tcx;
        let skip_analysis = HashSet::default();
        let selection = analyze::selection::Selection::of_crate(tcx);
        Self {
            ctx,
            tcx,
            skip_analysis,
            selection,
        }
    }

    pub fn run(&mut self) {
        let span = tracing::debug_span!("crate", krate = %self.tcx.crate_name(rustc_span::def_id::LOCAL_CRATE));
        let _guard = span.enter();

        self.analyze_raw_command_annot();
        self.register_trait_laws();
        self.report_unmatched_selection();
        self.refine_local_defs();
        let keys: Vec<_> = self.tcx.mir_keys(()).iter().copied().collect();
        self.ctx.record_hist_inv_specified_params(keys.into_iter());
        self.analyze_local_defs();
        self.ctx.emit_pending_pred_instances();
        self.ctx.emit_pending_laws();
        self.ctx.emit_fn_mut_instance_obligations();
        self.ctx.check_reused_spec_bounds();
        self.assert_callable_entry();
    }

    /// Records every `#[thrust::law]` function declared in a local trait.
    fn register_trait_laws(&mut self) {
        for item_id in self.tcx.hir_crate_items(()).trait_items() {
            let def_id = item_id.owner_id.to_def_id();
            let is_law = self
                .tcx
                .get_attrs_by_path(def_id, &analyze::annot::law_path())
                .next()
                .is_some();
            if !is_law {
                continue;
            }
            let trait_def_id = self
                .tcx
                .opt_associated_item(def_id)
                .and_then(|item| item.trait_container(self.tcx))
                .expect("a trait item has a trait");
            self.ctx.register_trait_law(trait_def_id, def_id);
        }
    }
}

/// Whether a generic def with a body is verified at each instance rather than once over its type
/// parameters (`THRUST_PER_INSTANCE_GENERICS=1`).
fn per_instance_generics() -> bool {
    matches!(
        std::env::var("THRUST_PER_INSTANCE_GENERICS").as_deref(),
        Ok("1")
    )
}
