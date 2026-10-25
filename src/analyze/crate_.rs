//! Analyze a local crate.

use std::collections::HashSet;

use rustc_hir::def_id::CRATE_DEF_ID;
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;
use crate::analyze::selection::ItemPath;
use crate::chc;
use crate::chc::debug;
use crate::pretty::PrettyDisplayExt as _;
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
    /// The fn-like defs whose bodies are trusted rather than analyzed: `#[thrust::trusted]` ones,
    /// those outside `THRUST_VERIFY_ONLY` that are trusted for their contract, and the closures in
    /// them.
    trusted: HashSet<LocalDefId>,
    selection: Option<analyze::selection::Selection>,
    body_checks: analyze::BodyChecks,
}

const TRUSTED_ATTR: &str = "#[thrust::trusted]";
const OUTSIDE_SELECTION: &str = "outside THRUST_VERIFY_ONLY, its written contract assumed";

/// What is done with the body of a closure in a function whose body is not analyzed, which
/// `enclosing` says.
fn enclosed(enclosing: Option<analyze::BodyCheck>) -> analyze::BodyCheck {
    use analyze::BodyCheck;
    match enclosing {
        Some(BodyCheck::Trusted(_)) => BodyCheck::Trusted("in a trusted function"),
        Some(BodyCheck::Ignored(_)) => BodyCheck::Ignored("in an ignored function"),
        Some(BodyCheck::Unselected(_)) => {
            BodyCheck::Unselected("in a function outside THRUST_VERIFY_ONLY")
        }
        Some(BodyCheck::Specification) => BodyCheck::Specification,
        _ => BodyCheck::NotAnalyzed("in a function whose body is not analyzed"),
    }
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
        let mut impl_methods_with_own_contract = Vec::new();
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
                    if self.tcx.def_kind(self.tcx.parent(target_def_id))
                        == (rustc_hir::def::DefKind::Impl { of_trait: true })
                    {
                        impl_methods_with_own_contract.push(target_def_id);
                    }
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
                        self.trusted.insert(local_target_def_id);
                        self.body_checks.record(
                            local_target_def_id,
                            analyze::BodyCheck::Trusted(TRUSTED_ATTR),
                        );
                    }
                }
                self.body_checks
                    .record(*local_def_id, analyze::BodyCheck::Specification);
                if matches!(
                    self.tcx.def_kind(target_def_id),
                    rustc_hir::def::DefKind::AssocFn
                ) {
                    trait_method_spec_keys.push(*local_def_id);
                    keys.swap_remove(local_def_id);
                }
            }
            if analyzer.is_crate_destructor() {
                check_destructor_annotations(self.tcx, &analyzer, *local_def_id);
            }
            if analyzer.is_annotated_as_ignored() && analyzer.has_contract_annotation() {
                self.tcx.dcx().span_err(
                    self.tcx.def_span(*local_def_id),
                    "`#[thrust::ignored]` cannot have a contract: an ignored function is invisible \
                     to Thrust and must not run; to trust a contract without checking the body, \
                     write `#[thrust::trusted]`",
                );
            }
            let ignored = if analyzer.is_annotated_as_ignored() {
                Some("#[thrust::ignored]")
            } else if analyzer.is_ignored_derive() {
                Some("a derived method")
            } else {
                None
            };
            if let Some(reason) = ignored {
                self.skip_analysis.insert(*local_def_id);
                self.body_checks
                    .record(*local_def_id, analyze::BodyCheck::Ignored(reason));
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
                self.body_checks
                    .record(*local_def_id, analyze::BodyCheck::Specification);
                keys.swap_remove(local_def_id);
            }
        }
        for def_id in impl_methods_with_own_contract {
            self.ctx.register_impl_method_with_own_contract(def_id);
        }
        // Nor is the body of a target outside `THRUST_VERIFY_ONLY`, whose contract the spec writes.
        for local_target_def_id in local_spec_targets {
            if self.is_outside_selection(local_target_def_id) {
                self.skip_analysis.insert(local_target_def_id);
                self.trusted.insert(local_target_def_id);
                self.body_checks.record(
                    local_target_def_id,
                    analyze::BodyCheck::Unselected(OUTSIDE_SELECTION),
                );
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

    /// Whether `local_def_id` is a function outside the selection of `THRUST_VERIFY_ONLY`
    /// whose body is trusted when its contract is written: a typeck root that is not a trait law.
    fn is_outside_selection(&self, local_def_id: LocalDefId) -> bool {
        let def_id = local_def_id.to_def_id();
        self.selection.as_ref().is_some_and(|selection| {
            self.tcx.typeck_root_def_id(def_id) == def_id
                && !self.is_trait_law(local_def_id)
                && !selection.contains(self.tcx, def_id)
        })
    }

    /// Reports each `THRUST_VERIFY_ONLY` entry that selects no function of the crate,
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

    #[tracing::instrument(
        skip(self),
        fields(
            def_id = %self.tcx.def_path_str(local_def_id),
            def_index = local_def_id.local_def_index.as_u32()
        )
    )]
    fn refine_fn_def(&mut self, local_def_id: LocalDefId) {
        let previous = self
            .ctx
            .enter_template_site(analyze::TemplateSite::Contract(local_def_id));
        self.refine_fn_def_at_site(local_def_id);
        self.ctx.leave_template_site(previous);
    }

    fn refine_fn_def_at_site(&mut self, local_def_id: LocalDefId) {
        let sig = self.ctx.fn_sig(local_def_id.to_def_id());
        let contract_generic = !self.tcx.is_closure_like(local_def_id.to_def_id())
            && self.ctx.contract_names_type_param(local_def_id);
        let is_law_impl = self.is_law_impl(local_def_id);
        let per_instance = self.ctx.per_instance_generics();
        let outside_selection = self.is_outside_selection(local_def_id);
        let mut analyzer = self.ctx.local_def_analyzer(local_def_id);

        if analyzer.is_annotated_as_trusted() {
            assert!(
                analyzer.is_fully_annotated(),
                "`#[thrust::trusted]` needs both `requires` and `ensures` (or `#[thrust::callable]`) on `{}`",
                self.tcx.def_path_str(local_def_id)
            );
            self.skip_analysis.insert(local_def_id);
            self.trusted.insert(local_def_id);
            self.body_checks
                .record(local_def_id, analyze::BodyCheck::Trusted(TRUSTED_ATTR));
        }

        let is_injected_std = analyzer.is_injected_std();
        if is_injected_std {
            self.skip_analysis.insert(local_def_id);
        }

        // A derived method has the contract of its trait method, which its derive implies. A
        // generic one is a generic def with that contract, so that at an instance where the trait
        // method's spec does not apply its body is analyzed (`Analyzer::def_ty_with_args`).
        let trusted_derive = analyzer.is_trusted_derive() && analyzer.trait_item_ty().is_some();
        if trusted_derive {
            analyzer.check_derived_field_impls();
            analyzer.check_derive_keeps_invariant();
            self.skip_analysis.insert(local_def_id);
            self.body_checks.record(
                local_def_id,
                analyze::BodyCheck::NotAnalyzed(
                    "a derived method, with the contract of its trait method",
                ),
            );
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
                let enclosing = self.body_checks.get(root_local_def_id);
                self.body_checks.record(local_def_id, enclosed(enclosing));
                if self.trusted.contains(&root_local_def_id) {
                    self.trusted.insert(local_def_id);
                }
                return;
            }
        }

        // Outside `THRUST_VERIFY_ONLY`, a function whose contract leaves nothing to infer from its
        // body is trusted, as `#[thrust::trusted]` is; one with a predicate variable in its
        // contract is analyzed, because its callers use the contract inferred from its body.
        let mut expected = None;
        if outside_selection && !self.skip_analysis.contains(&local_def_id) {
            let ty = analyzer.expected_ty();
            if !ty.has_pred_var() {
                tracing::debug!("trusted outside THRUST_VERIFY_ONLY");
                self.skip_analysis.insert(local_def_id);
                self.trusted.insert(local_def_id);
                self.body_checks.record(
                    local_def_id,
                    analyze::BodyCheck::Unselected(OUTSIDE_SELECTION),
                );
            }
            expected = Some(ty);
        }

        let owner_fn_id = analyzer.owner_fn_id;
        let owner_fn_id_args = analyzer.owner_fn_id_args;
        use mir_ty::TypeVisitableExt as _;
        let trait_method = self.tcx.trait_of_assoc(owner_fn_id).is_some();
        if analyzer.is_annotated_as_extern_spec_fn()
            && is_narrower_local_spec(self.tcx, local_def_id, owner_fn_id, owner_fn_id_args)
        {
            // The spec covers the local target only at some of its instances, so it is not the
            // contract of the target's generic body: the body is analyzed at each covered
            // instance a call reaches, in the caller's environment, against the spec there
            // (`Analyzer::def_ty_with_args`). Checked over the target's own type parameters, the
            // spec's types, normalized under the spec's bounds or at its fixed arguments,
            // disagree with the body's. A trusted target, or one outside `THRUST_VERIFY_ONLY`,
            // is not analyzed.
            let skips_target = owner_fn_id
                .as_local()
                .is_some_and(|def_id| self.skip_analysis.contains(&def_id));
            if skips_target {
                self.ctx.register_deferred_def_without_analysis(
                    owner_fn_id,
                    local_def_id,
                    owner_fn_id_args,
                );
            } else {
                self.ctx
                    .register_deferred_def(owner_fn_id, local_def_id, owner_fn_id_args);
            }
        } else if sig.has_param() || trait_method || contract_generic {
            // A function is generic when its contract names a type parameter its signature does
            // not mention: a trait method's `Self::score(x)`, or `T::score(x)` of
            // `fn via<T: Score>`, resolves at each instance to the impl's own logic function.
            // Closures keep their treatment.
            if trusted_derive {
                let expected = analyzer.expected_ty();
                self.ctx
                    .register_generic_def(owner_fn_id, local_def_id, Some(expected));
            } else if owner_fn_id.as_local().is_none_or(|def_id| {
                self.skip_analysis.contains(&def_id) || !self.tcx.is_mir_available(def_id)
            }) {
                self.body_checks.record(
                    local_def_id,
                    analyze::BodyCheck::NotAnalyzed("generic, with no body to analyze"),
                );
                self.ctx.register_deferred_def_without_analysis(
                    owner_fn_id,
                    local_def_id,
                    owner_fn_id_args,
                );
            } else if per_instance && !analyzer.is_crate_destructor() {
                // A destructor is checked once over its type parameters even so (D57): `std` may
                // drop it at an instance that no call site of the crate reaches.
                // Upstream Thrust's treatment: the body is analyzed at each instance a call site
                // reaches, and not once over the type parameters.
                self.body_checks.record(
                    local_def_id,
                    analyze::BodyCheck::NotAnalyzed(
                        "generic, analyzed at each instance a call reaches, and none does",
                    ),
                );
                self.ctx
                    .register_deferred_def(owner_fn_id, local_def_id, owner_fn_id_args);
            } else {
                let expected = expected.unwrap_or_else(|| analyzer.expected_ty());
                self.ctx
                    .register_generic_def(owner_fn_id, local_def_id, Some(expected));
            }
        } else if is_injected_std && is_law_impl {
            // The contract of an injected impl's law instantiates the trait's predicates at the
            // impl; it is built where a proof step calls the law, not in every crate.
            self.ctx.register_deferred_def_without_analysis(
                owner_fn_id,
                local_def_id,
                owner_fn_id_args,
            );
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
                self.body_checks.record(
                    *local_def_id,
                    analyze::BodyCheck::NotAnalyzed(
                        "a law, checked at the impls that inherit it, and none was",
                    ),
                );
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

    /// Checks that the contract written on a method of a local trait impl refines the trait's
    /// contract of that method at the impl, as Creusot does for each method of an impl
    /// (`translation/traits.rs`, `translate_impl`): under the trait's precondition the impl's
    /// holds, and the impl's postcondition implies the trait's. The trait's contract is the one
    /// a call through a type parameter bounded by the trait uses: an extern spec of a std trait's
    /// method, which may hold only under a bound of its own (`I: IteratorSpec` of
    /// `Iterator::next`), or a local trait's. A method without a contract of its own takes the
    /// trait's (`local_def::Analyzer::expected_ty`), so its body is checked against it directly.
    fn check_impl_refinements(&mut self) {
        for def_id in self.ctx.impl_methods_with_own_contract() {
            if self
                .selection
                .as_ref()
                .is_some_and(|selection| !selection.contains(self.tcx, def_id))
            {
                continue;
            }
            let impl_ty = self.ctx.concrete_def_ty(def_id).cloned();
            let Some(trait_ty) = self
                .ctx
                .local_def_analyzer(def_id.expect_local())
                .trait_item_ty()
            else {
                continue;
            };
            // A trusted method of a generic impl is deferred, with no type registered.
            let impl_ty = impl_ty.unwrap_or_else(|| {
                let identity = mir_ty::GenericArgs::identity_for_item(self.tcx, def_id);
                self.ctx
                    .def_ty_with_args(def_id, identity, def_id)
                    .expect("an impl method's own contract over the impl's generics")
            });
            tracing::info!(
                ?def_id,
                impl_ty = %impl_ty.display(),
                trait_ty = %trait_ty.display(),
                "impl refinement"
            );
            let clauses = crate::rty::relate_refining_function_type(
                impl_ty.ty.as_function().unwrap(),
                trait_ty.ty.as_function().unwrap(),
                Some(&self.ctx.enum_defs),
            );
            self.ctx.extend_clauses(clauses);
        }
    }

    /// Whether `local_def_id` is an impl's definition of a `#[thrust::law]` of its trait.
    fn is_law_impl(&self, local_def_id: LocalDefId) -> bool {
        self.tcx
            .opt_associated_item(local_def_id.to_def_id())
            .and_then(|item| item.trait_item_def_id)
            .is_some_and(|trait_item| {
                self.tcx
                    .get_attrs_by_path(trait_item, &analyze::annot::law_path())
                    .next()
                    .is_some()
            })
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
                let trait_ref = self
                    .tcx
                    .impl_trait_ref(impl_def_id)
                    .unwrap()
                    .instantiate_identity();
                // Checked at each instance instead (`check_instance_laws`).
                if self.ctx.per_instance_law_impls.contains(&impl_def_id) {
                    continue;
                }
                let args = self.tcx.erase_regions(trait_ref.args);
                for law_def_id in &laws {
                    self.check_inherited_law(impl_def_id, *law_def_id, args);
                }
            }
        }
    }

    /// A law inherited by a local impl that cannot be checked there is an error: a law is assumed
    /// at every type parameter of its trait only because each impl proves it.
    fn report_unchecked_inherited_law(&self, law_def_id: DefId, impl_def_id: DefId, what: &str) {
        self.tcx.dcx().span_err(
            self.tcx.def_span(impl_def_id),
            format!(
                "the law `{}` this impl inherits has {what} to check it against here",
                self.tcx.def_path_str(law_def_id)
            ),
        );
    }

    /// Checks the trait law `law_def_id`, which `impl_def_id` inherits, at the trait arguments
    /// `args` of the impl (its own, or an instance's), and returns whether it did.
    fn check_inherited_law(
        &mut self,
        impl_def_id: DefId,
        law_def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> bool {
        if self
            .tcx
            .impl_item_implementor_ids(impl_def_id)
            .contains_key(&law_def_id)
        {
            return false;
        }
        // The laws are typed under one of the impl's functions, or under the impl itself when it
        // has none: its laws are assumed at type parameters all the same.
        let owner = self
            .tcx
            .associated_item_def_ids(impl_def_id)
            .iter()
            .copied()
            .find(|id| self.tcx.def_kind(*id).is_fn_like())
            .unwrap_or(impl_def_id);
        if self
            .selection
            .as_ref()
            .is_some_and(|s| !s.contains_inherited(self.tcx, impl_def_id, law_def_id))
        {
            tracing::info!(
                ?law_def_id,
                ?impl_def_id,
                "inherited law assumed outside THRUST_VERIFY_ONLY"
            );
            return false;
        }
        let Some(law_local) = law_def_id.as_local() else {
            return false;
        };
        if !self.tcx.is_mir_available(law_def_id) {
            self.report_unchecked_inherited_law(law_def_id, impl_def_id, "no body");
            return false;
        }
        tracing::info!(
            ?law_def_id,
            ?impl_def_id,
            ?args,
            "inherited law checked at impl"
        );
        if !self.check_law_body(law_local, law_def_id, args, args, owner) {
            self.report_unchecked_inherited_law(law_def_id, impl_def_id, "no contract");
            return false;
        }
        self.ctx.inherited_law_checked(impl_def_id, law_def_id);
        true
    }

    /// Analyzes `body`, a law's proof (the trait's default body or an impl's own), at `body_args`
    /// against the contract of the trait law `law_def_id` at the trait arguments `trait_args`, and
    /// returns whether it did.
    fn check_law_body(
        &mut self,
        body: LocalDefId,
        law_def_id: DefId,
        trait_args: mir_ty::GenericArgsRef<'tcx>,
        body_args: mir_ty::GenericArgsRef<'tcx>,
        owner: DefId,
    ) -> bool {
        // A trait method with a default body carries its contract on the spec function the macro
        // generates, so the contract is read as a call site reads it, at the impl's arguments.
        // An impl's own proof is analyzed only here; reading the contract as a call site does
        // would analyze the trait's default body there as well.
        let own = body.to_def_id() != law_def_id;
        let expected = if own {
            self.ctx.contract_with_args(law_def_id, trait_args, owner)
        } else {
            self.ctx.def_ty_with_args(law_def_id, trait_args, owner)
        };
        let Some(expected) = expected else {
            tracing::warn!(?law_def_id, ?trait_args, "law has no contract");
            return false;
        };
        let mut analyzer = self.ctx.local_def_analyzer(body);
        analyzer.owner_fn_id(owner).generic_args(body_args);
        analyzer.run(&expected);
        self.ctx.instance_law_checked(law_def_id, trait_args);
        true
    }

    /// Checks the laws of each impl of `per_instance_law_impls` at each instance the crate uses
    /// (`THRUST_PER_INSTANCE_GENERICS`), as the impl's functions are analyzed there: where a derived
    /// predicate the impl's type leaves out is requested, at that type for every such impl, and
    /// where a law's contract is used. An inherited law is checked as at a concrete impl; a law the
    /// impl writes is analyzed at the instance. A check may use more instances, so it runs to a
    /// fixed point; [`derived_pred::check_law_uses`] rejects a use found later.
    fn check_instance_laws(&mut self) {
        let mut checked: HashSet<(DefId, mir_ty::GenericArgsRef<'tcx>)> = HashSet::new();
        loop {
            let instances: Vec<_> = self
                .instances_to_check()
                .into_iter()
                .filter(|instance| !checked.contains(instance))
                .collect();
            if instances.is_empty() {
                return;
            }
            for (trait_def_id, trait_args) in instances {
                checked.insert((trait_def_id, trait_args));
                self.check_laws_at(trait_def_id, trait_args);
            }
        }
    }

    /// The (trait, concrete trait arguments) pairs that select an impl of
    /// `per_instance_law_impls` and are used so far.
    fn instances_to_check(&self) -> Vec<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        let tcx = self.tcx;
        let law_uses = self.ctx.law_uses().into_iter().filter_map(|(law, args)| {
            let trait_def_id = tcx.trait_of_assoc(law)?;
            Some((
                trait_def_id,
                tcx.erase_regions(args.truncate_to(tcx, tcx.generics_of(trait_def_id))),
            ))
        });
        let derived_self_tys: Vec<mir_ty::Ty<'tcx>> = self
            .ctx
            .pending_pred_instance_requests()
            .into_iter()
            .filter(|(pred_def_id, _)| self.ctx.is_derived_predicate(*pred_def_id))
            .filter_map(|(pred_def_id, args)| {
                analyze::derived_pred::generic_impl_instance(tcx, pred_def_id, args)
            })
            .map(|(_, trait_args)| trait_args.type_at(0))
            .collect();
        // Every trait with an impl of the set, at each type a derived predicate is requested at.
        // Only traits with no parameter beside `Self`, whose arguments the type alone gives; a
        // law of another trait is checked where its contract is used (`law_uses`), and a use not
        // checked is rejected (`derived_pred::check_law_uses`). Sorted, so that the checks, and
        // the query, come in one order.
        let mut law_traits: Vec<DefId> = self
            .ctx
            .per_instance_law_impls
            .iter()
            .filter_map(|impl_def_id| tcx.trait_id_of_impl(*impl_def_id))
            .filter(|trait_def_id| tcx.generics_of(*trait_def_id).count() == 1)
            .collect();
        law_traits.sort_by_key(|trait_def_id| tcx.def_path_hash(*trait_def_id));
        law_traits.dedup();
        let at_derived = derived_self_tys.iter().flat_map(|ty| {
            law_traits
                .iter()
                .map(|trait_def_id| (*trait_def_id, tcx.mk_args(&[(*ty).into()])))
        });
        law_uses
            .chain(at_derived)
            .filter(|(trait_def_id, trait_args)| {
                analyze::derived_pred::select_generic_impl(tcx, *trait_def_id, trait_args)
                    .is_some_and(|(impl_def_id, _)| {
                        self.ctx.per_instance_law_impls.contains(&impl_def_id)
                    })
            })
            .collect()
    }

    /// Checks each law of `trait_def_id` at the concrete `trait_args`, at the impl of
    /// `per_instance_law_impls` they select.
    fn check_laws_at(&mut self, trait_def_id: DefId, trait_args: mir_ty::GenericArgsRef<'tcx>) {
        let Some((impl_def_id, impl_args)) =
            analyze::derived_pred::select_generic_impl(self.tcx, trait_def_id, trait_args)
        else {
            return;
        };
        let laws = self
            .ctx
            .trait_laws
            .borrow()
            .get(&trait_def_id)
            .cloned()
            .unwrap_or_default();
        let implemented = self.tcx.impl_item_implementor_ids(impl_def_id);
        for law_def_id in laws {
            let Some(own) = implemented.get(&law_def_id) else {
                self.check_inherited_law(impl_def_id, law_def_id, trait_args);
                continue;
            };
            // The impl's own proof, at the instance, against the trait's contract there.
            if let Some(own_local) = own.as_local() {
                self.check_law_body(own_local, law_def_id, trait_args, impl_args, *own);
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
        let selection = analyze::selection::Selection::from_env();
        let body_checks = ctx.body_checks();
        Self {
            ctx,
            tcx,
            skip_analysis,
            trusted: HashSet::new(),
            selection,
            body_checks,
        }
    }

    /// Stops at a `Model` impl of the crate whose model holds a value without a model (a `str`, a
    /// raw or function pointer, a trait object; `model_eq::modelless_part`), such as `impl Model
    /// for S { type Ty = S; }` of a struct holding a `&str`: the part has the null sort, so a
    /// specification comparing models of the type, also at a type parameter instantiated with it,
    /// would hold of any two values (`==`) or of none (`!=`).
    fn check_model_impls(&self) {
        let Some(model_ty) = self.ctx.def_ids().model_ty() else {
            return;
        };
        let model_trait = self.tcx.parent(model_ty);
        for &impl_did in self.tcx.local_trait_impls(model_trait) {
            let Some(assoc) = self
                .tcx
                .associated_items(impl_did.to_def_id())
                .in_definition_order()
                .find(|item| item.trait_item_def_id == Some(model_ty))
            else {
                continue;
            };
            let ty = self.tcx.type_of(assoc.def_id).instantiate_identity();
            if let Some(part) = analyze::model_eq::modelless_part(self.tcx, model_trait, ty) {
                self.tcx.dcx().span_fatal(
                    self.tcx.def_span(impl_did),
                    format!(
                        "thrust: the model `{ty}` holds `{part}`, which has no model, so \
                         specifications could not tell its values apart"
                    ),
                );
            }
        }
    }

    pub fn run(&mut self) {
        let span = tracing::debug_span!("crate", krate = %self.tcx.crate_name(rustc_span::def_id::LOCAL_CRATE));
        let _guard = span.enter();

        let proof_branch = self.ctx.def_ids().proof_branch();
        analyze::lemma::check_lemmas(self.tcx, proof_branch);
        self.check_model_impls();
        self.ctx.check_associated_types_without_invariant();
        self.analyze_raw_command_annot();
        self.register_trait_laws();
        self.check_restated_laws();
        self.report_unmatched_selection();
        self.refine_local_defs();
        self.check_impl_refinements();
        analyze::lemma::check_proof_branches(self.tcx, proof_branch, |def_id| {
            !self.skip_analysis.contains(&def_id)
        });
        let keys: Vec<_> = self.tcx.mir_keys(()).iter().copied().collect();
        self.ctx.record_hist_inv_specified_params(keys.into_iter());
        self.ctx.set_trusted_bodies(self.trusted.clone());
        if self.ctx.per_instance_generics() {
            self.ctx.per_instance_law_impls = analyze::derived_pred::per_instance_law_impls(
                self.tcx,
                &self.ctx.trait_laws.borrow(),
            );
        }
        self.analyze_local_defs();
        self.fix_entered_preconditions();
        self.check_instance_laws();
        self.ctx.emit_pending_pred_instances();
        self.ctx.emit_pending_laws();
        self.ctx.emit_fn_mut_instance_obligations();
        self.ctx.check_reused_instances();
        self.ctx.check_derived_predicates();
        self.check_ignored_not_run();
        self.assert_callable_entry();
    }

    /// Checks that each `#[thrust::law]` restated on an impl item (as Creusot writes it)
    /// implements a law of a trait.
    fn check_restated_laws(&self) {
        for item_id in self.tcx.hir_crate_items(()).impl_items() {
            let local_def_id = item_id.owner_id.def_id;
            let restated = self
                .tcx
                .get_attrs_by_path(local_def_id.to_def_id(), &analyze::annot::law_path())
                .next()
                .is_some();
            if restated && !self.is_law_impl(local_def_id) {
                self.tcx.dcx().span_err(
                    self.tcx.def_span(local_def_id),
                    "`#[thrust_macros::law]` on a method that implements no law of a trait",
                );
            }
        }
    }

    /// Checks that no function Thrust verifies can run an ignored one
    /// ([`analyze::Analyzer::stop_ignored_reached`]): the roots are the fn-like defs whose bodies
    /// are analyzed, monomorphic ones as instances and generic ones through their instances.
    fn check_ignored_not_run(&self) {
        let (roots, generic) = self.walk_roots();
        self.ctx
            .stop_ignored_reached(roots, generic, |def_id| self.crate_mode(def_id));
    }

    /// The roots of the walks over what the crate can run: the fn-like defs whose bodies are
    /// analyzed, monomorphic ones as instances and generic ones by def, the monomorphic trusted
    /// functions and the entry function.
    fn walk_roots(&self) -> (Vec<mir_ty::Instance<'tcx>>, Vec<rustc_span::def_id::DefId>) {
        let analyzed = self.tcx.mir_keys(()).iter().copied().filter(|def_id| {
            let id = def_id.to_def_id();
            !self.skip_analysis.contains(def_id)
                && self.tcx.def_kind(id).is_fn_like()
                && !self.tcx.is_closure_like(id)
        });
        let (generic, monomorphic): (Vec<_>, Vec<_>) =
            analyzed.map(LocalDefId::to_def_id).partition(|def_id| {
                self.tcx
                    .generics_of(*def_id)
                    .requires_monomorphization(self.tcx)
            });
        // A trusted function and the entry function are roots too: a trusted body may run
        // verified code, which may not run an ignored function, though no verified caller exists.
        let trusted = self
            .trusted
            .iter()
            .map(|def_id| def_id.to_def_id())
            .filter(|def_id| {
                !self.tcx.is_closure_like(*def_id)
                    && !self
                        .tcx
                        .generics_of(*def_id)
                        .requires_monomorphization(self.tcx)
            });
        let entry = self.tcx.entry_fn(()).map(|(def_id, _)| def_id);
        let roots = monomorphic
            .into_iter()
            .chain(trusted)
            .chain(entry)
            .map(|def_id| mir_ty::Instance::mono(self.tcx, def_id))
            .collect();
        (roots, generic)
    }

    /// The mode of a crate function on the ignored walk ([`analyze::Mode`]).
    fn crate_mode(&self, def_id: rustc_span::def_id::DefId) -> Option<analyze::Mode> {
        let local = def_id.as_local()?;
        if self.trusted.contains(&local) {
            return Some(analyze::Mode::Trusted);
        }
        // A derived impl is not trusted by the user: its methods rely on the fields' impls.
        let derived = self
            .tcx
            .impl_of_assoc(def_id)
            .is_some_and(|impl_did| self.tcx.is_automatically_derived(impl_did));
        if derived {
            return Some(analyze::Mode::Verified);
        }
        self.is_analyzed(def_id).then_some(analyze::Mode::Verified)
    }

    /// Whether `def_id` is a fn-like def of the crate whose body Thrust analyzes.
    fn is_analyzed(&self, def_id: rustc_span::def_id::DefId) -> bool {
        def_id.as_local().is_some_and(|local| {
            self.tcx.def_kind(def_id).is_fn_like() && !self.skip_analysis.contains(&local)
        })
    }

    /// Fixes the precondition of each crate function with an inferred contract that code Thrust
    /// does not analyze can run ([`analyze::unanalyzed_entry`]): a function or method entered
    /// so is checked under its precondition holding of every argument, unless the entering
    /// contract names it with `pre!`, and a closure must have been handed over, with its
    /// obligation, by the analyzed call that leads into the code that runs it. The closures are
    /// checked on a second walk, after the bodies the first one's entries analyze at new
    /// instances have recorded their hand-overs.
    fn fix_entered_preconditions(&mut self) {
        let entries = self.unanalyzed_entries();
        for (callee, from, ty) in &entries.escaping {
            self.stop_escaping_callable(*callee, *from, *ty);
        }
        let mut fixed = HashSet::new();
        for (callee, from) in &entries.items {
            if !fixed.insert(*callee) {
                continue;
            }
            self.stop_unanalyzed_closure_arg(*callee, *from);
            let Some(fn_ty) = self.ctx.entered_inferred_fn_ty(*callee) else {
                continue;
            };
            tracing::debug!(%callee, "entered from code Thrust does not analyze");
            let clauses = analyze::Analyzer::accepts_every_argument(&fn_ty);
            self.ctx.extend_clauses(clauses);
        }
        for (closure, from) in self.unanalyzed_entries().unhanded_closures {
            let def_id = closure.def_id();
            if self.ctx.has_written_requires(def_id) {
                continue;
            }
            self.tcx.dcx().span_fatal(
                self.tcx.def_span(def_id),
                format!(
                    "`{from}`, which Thrust does not analyze, can run the closure `{closure}`, \
                     whose precondition is inferred, without an analyzed call handing it over \
                     to it with its obligation: give the closure a `requires` with \
                     `thrust_macros::closure!`"
                ),
            );
        }
    }

    /// Stops at a closure of the crate with an inferred precondition, or a function pointer,
    /// that the analyzed `callee` hands to `from`, which Thrust does not analyze, by returning
    /// it or storing it behind a `&mut`: no hand-over states its obligation. A closure with a
    /// written `requires`, or one of a trusted body, is trusted to be called as it says.
    fn stop_escaping_callable(
        &self,
        callee: mir_ty::Instance<'tcx>,
        from: mir_ty::Instance<'tcx>,
        ty: mir_ty::Ty<'tcx>,
    ) {
        let remedy = match *ty.kind() {
            mir_ty::TyKind::Closure(def_id, _) => {
                if !self.is_analyzed(def_id) || self.ctx.has_written_requires(def_id) {
                    return;
                }
                "give the closure a `requires` with `thrust_macros::closure!`"
            }
            _ => "keep the function pointer in verified code",
        };
        self.tcx.dcx().span_fatal(
            self.tcx.def_span(callee.def_id()),
            format!(
                "`{callee}` gives `{ty}` to `{from}`, which Thrust does not analyze, and nothing \
                 requires its precondition there: {remedy}"
            ),
        );
    }

    /// Stops at `callee`, entered from `from`, which Thrust does not analyze, at a closure of a
    /// body Thrust does not analyze either: such a closure has no contract to check `callee`'s
    /// body against.
    fn stop_unanalyzed_closure_arg(
        &self,
        callee: mir_ty::Instance<'tcx>,
        from: mir_ty::Instance<'tcx>,
    ) {
        let closure = callee
            .args
            .types()
            .flat_map(|ty| ty.walk())
            .find_map(|arg| match arg.as_type().map(|ty| *ty.kind()) {
                Some(mir_ty::TyKind::Closure(def_id, _))
                    if def_id.is_local() && !self.is_analyzed(def_id) =>
                {
                    Some(def_id)
                }
                _ => None,
            });
        let Some(closure) = closure else {
            return;
        };
        let written = self
            .ctx
            .concrete_def_ty(callee.def_id())
            .and_then(|def_ty| def_ty.ty.as_function())
            .is_some_and(|fn_ty| !self.ctx.infers_precondition(fn_ty));
        if written {
            return;
        }
        self.tcx.dcx().span_fatal(
            self.tcx.def_span(callee.def_id()),
            format!(
                "`{from}`, which Thrust does not analyze, runs `{callee}` at the closure `{}` of \
                 a body Thrust does not analyze either, which has no contract to check it \
                 against: give `{}` a contract",
                self.tcx.def_path_str(closure),
                self.tcx.def_path_str(callee.def_id()),
            ),
        );
    }

    fn unanalyzed_entries(&self) -> analyze::unanalyzed_entry::Entries<'tcx> {
        let (roots, generic) = self.walk_roots();
        let roots = self.ctx.walk_roots(roots, generic, |def_id| {
            self.crate_mode(def_id) == Some(analyze::Mode::Verified)
        });
        self.ctx
            .unanalyzed_entries(roots, |def_id| self.is_analyzed(def_id))
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

/// A `Drop::drop` of the crate is verified once under `requires(true)` and its postcondition
/// inferred (D57): Rust runs it wherever a value is dropped, also in code Thrust does not
/// analyze. So it takes no written contract, and is neither trusted nor ignored.
fn check_destructor_annotations<'tcx>(
    tcx: TyCtxt<'tcx>,
    analyzer: &analyze::local_def::Analyzer<'tcx, '_>,
    local_def_id: LocalDefId,
) {
    let span = tcx.def_span(local_def_id);
    if analyzer.has_contract_annotation() {
        tcx.dcx().span_err(span, DESTRUCTOR_CONTRACT_ERROR);
    }
    if analyzer.is_annotated_as_trusted() || analyzer.is_annotated_as_ignored() {
        tcx.dcx().span_err(
            span,
            "a `Drop::drop` cannot be `#[thrust::trusted]` or `#[thrust::ignored]`: Rust runs \
             it wherever a value is dropped, so Thrust verifies it",
        );
    }
}

/// The error for a written contract on a `Drop::drop`; `thrust_macros::context` gives the same.
const DESTRUCTOR_CONTRACT_ERROR: &str = "a `Drop::drop` takes no `requires` or `ensures`: Rust runs \
     it wherever a value is dropped, so Thrust checks it under `requires(true)` and infers its effect";

/// Whether `THRUST_PER_INSTANCE_GENERICS=1` asks for each generic def with a body to be verified
/// at each instance rather than once over its type parameters.
pub(super) fn per_instance_generics_requested() -> bool {
    matches!(
        std::env::var("THRUST_PER_INSTANCE_GENERICS").as_deref(),
        Ok("1")
    )
}

/// Whether `local_def_id` is an extern spec of a function of this crate, `target`, that covers
/// only some of its instances: it calls the target at an argument that is not one of the
/// spec's type parameters, or bounds an associated type the target leaves free (`R:
/// IntoSliceIdx<I, [T], Output = usize>` where the target has `R: IntoSliceIdx<I, [T]>`). The
/// spec `requires`/`ensures` generate for a function repeats its bounds, so it covers all of it.
fn is_narrower_local_spec<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,
    target: rustc_span::def_id::DefId,
    target_args: Option<mir_ty::GenericArgsRef<'tcx>>,
) -> bool {
    let Some(target_args) = target_args else {
        return false;
    };
    if !target.is_local() {
        return false;
    }
    let fixes_an_arg = target_args
        .types()
        .any(|ty| !matches!(ty.kind(), mir_ty::TyKind::Param(_)));
    if fixes_an_arg {
        return true;
    }
    let target_projections: Vec<_> = tcx
        .predicates_of(target)
        .instantiate(tcx, target_args)
        .predicates
        .into_iter()
        .filter(|clause| clause.as_projection_clause().is_some())
        .map(|clause| tcx.erase_regions(clause))
        .collect();
    tcx.predicates_of(local_def_id)
        .predicates
        .iter()
        .filter(|(clause, _)| clause.as_projection_clause().is_some())
        .any(|(clause, _)| !target_projections.contains(&tcx.erase_regions(*clause)))
}
