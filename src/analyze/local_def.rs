//! Analyze a local definition.

use std::collections::{HashMap, HashSet};

use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt, TypeAndMut};
use rustc_mir_dataflow::impls::{
    EverInitializedPlaces, MaybeInitializedPlaces, MaybeLiveLocals, MaybeUninitializedPlaces,
};
use rustc_mir_dataflow::move_paths::{MoveData, MovePathIndex};
use rustc_mir_dataflow::{Analysis as _, MaybeReachable};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze;
use crate::analyze::did_cache::InvariantMarker;
use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{self, BasicBlockType, TypeBuilder};
use crate::rty;

fn stmt_str_literal(stmt: &rustc_hir::Stmt) -> Option<String> {
    use rustc_ast::LitKind;
    use rustc_hir::{Expr, ExprKind, Stmt, StmtKind};

    match stmt {
        Stmt {
            kind:
                StmtKind::Semi(Expr {
                    kind:
                        ExprKind::Lit(rustc_hir::Lit {
                            node: LitKind::Str(symbol, _),
                            ..
                        }),
                    ..
                }),
            ..
        } => Some(symbol.to_string()),
        _ => None,
    }
}

fn is_annotated_as_extern_spec_fn_impl(tcx: &TyCtxt, local_def_id: &LocalDefId) -> bool {
    tcx.get_attrs_by_path(
        local_def_id.to_def_id(),
        &analyze::annot::extern_spec_fn_path(),
    )
    .next()
    .is_some()
}

/// Extract the target DefId and the generic arguments the spec's own tail call reached it
/// with, from a `#[thrust::extern_spec_fn]` function.
///
/// The target is identified as the tail call expression (last expression without
/// semicolon) in the function body block. The arguments are in the target's own parameter
/// space (e.g. `[T, usize, Global]` for a spec of `Vec::index` fixing `Idx = usize`); a
/// position that is not one of the spec's own type parameters is one the spec's own source
/// fixed to a concrete type, and [`Analyzer::def_ty_with_args`] uses this to tell whether a
/// later call's actual instantiation is the one the spec covers.
fn extern_spec_fn_target_def_id_impl<'tcx>(
    tcx: &TyCtxt<'tcx>,
    local_def_id: &LocalDefId,
    mir_body: &Body<'tcx>,
) -> (DefId, mir_ty::GenericArgsRef<'tcx>) {
    let hir_node = tcx.hir_node_by_def_id(*local_def_id);
    let hir_body_id = match hir_node {
        rustc_hir::Node::Item(item) => {
            let rustc_hir::ItemKind::Fn { body: body_id, .. } = item.kind else {
                panic!("extern_spec_fn must be a function");
            };
            body_id
        }
        rustc_hir::Node::ImplItem(impl_item) => {
            let rustc_hir::ImplItemKind::Fn(_, body_id) = impl_item.kind else {
                panic!("extern_spec_fn must be a function");
            };
            body_id
        }
        rustc_hir::Node::TraitItem(trait_item) => {
            let rustc_hir::TraitItemKind::Fn(_, rustc_hir::TraitFn::Provided(body_id)) =
                trait_item.kind
            else {
                panic!("extern_spec_fn must be a function with a body");
            };
            body_id
        }
        _ => panic!("extern_spec_fn must be a function item or impl item"),
    };

    let hir_body = tcx.hir_body(hir_body_id);

    // The body is a block; the tail expression is the function call to the target.
    let rustc_hir::ExprKind::Block(block, _) = &hir_body.value.kind else {
        panic!("extern_spec_fn body must be a block");
    };
    let tail_expr = block
        .expr
        .expect("extern_spec_fn block must end with a tail call expression");

    let rustc_hir::ExprKind::Call(func_expr, _) = &tail_expr.kind else {
        panic!("extern_spec_fn tail expression must be a function call");
    };
    let rustc_hir::ExprKind::Path(qpath) = &func_expr.kind else {
        panic!("extern_spec_fn call must be a path expression");
    };

    let typeck_result = tcx.typeck(local_def_id);
    let hir_id = func_expr.hir_id;
    let rustc_hir::def::Res::Def(_, def_id) = typeck_result.qpath_res(qpath, hir_id) else {
        panic!("extern_spec_fn call must resolve to a definition");
    };

    let args = typeck_result.node_args(hir_id);
    let typing_env = mir_body.typing_env(*tcx);
    let instance = mir_ty::Instance::try_resolve(*tcx, typing_env, def_id, args).unwrap();
    if let Some(instance) = instance {
        (instance.def_id(), instance.args)
    } else {
        (def_id, args)
    }
}

/// An implementation of the typing of local definitions.
///
/// The current implementation only applies to function definitions. The entry point is
/// [`Analyzer::run`], which generates constraints during typing, given the expected type of the function.
pub struct Analyzer<'tcx, 'ctx> {
    ctx: &'ctx mut analyze::Analyzer<'tcx>,
    tcx: TyCtxt<'tcx>,

    local_def_id: LocalDefId,
    pub owner_fn_id: DefId,
    /// `owner_fn_id`'s generic arguments at the extern spec's own tail call, in `owner_fn_id`'s
    /// parameter space; `None` when this def is not an extern spec (then `owner_fn_id` is its
    /// own def_id and every call to it already shares its full generic space).
    pub owner_fn_id_args: Option<mir_ty::GenericArgsRef<'tcx>>,

    body: Body<'tcx>,
    /// the instantiation of the def's generic parameters being analyzed, also used
    /// to substitute HIR types during translation in [`crate::analyze::annot_fn`]
    generic_args: mir_ty::GenericArgsRef<'tcx>,
    drop_points: HashMap<BasicBlock, analyze::basic_block::DropPoints>,
    type_builder: TypeBuilder<'tcx>,
}

/// The locals that the move paths `paths` are parts of.
fn locals_of<'tcx>(
    paths: impl Iterator<Item = MovePathIndex>,
    move_data: &MoveData<'tcx>,
) -> HashSet<Local> {
    paths
        .map(|path| move_data.move_paths[path].place.local)
        .collect()
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    pub fn analyze_predicate_definition(&self) {
        let (sig, body) = self.predicate_definition();
        self.ctx.system.borrow_mut().push_pred_define(
            refine::user_defined_pred(self.tcx, self.local_def_id.to_def_id()),
            sig,
            body,
        );
    }

    /// The signature and the SMT-LIB2 body of a `#[thrust_macros::predicate]`.
    ///
    /// The signature is read off the (possibly instantiated) body, so setting
    /// [`Self::generic_args`] first yields the signature at that instantiation.
    pub fn predicate_definition(&self) -> (chc::UserDefinedPredSig, String) {
        // function's body
        use rustc_hir::{Block, Expr, ExprKind};

        let hir_body = self.tcx.hir_maybe_body_owned_by(self.local_def_id).unwrap();

        let predicate_body = match hir_body.value {
            Expr {
                kind: ExprKind::Block(Block { stmts, .. }, _),
                ..
            } => stmts
                .iter()
                .find_map(stmt_str_literal)
                .expect("invalid predicate definition: no string literal was found."),
            _ => panic!("expected function body, got: {hir_body:?}"),
        };

        // names and sorts of arguments
        let arg_names = self
            .tcx
            .fn_arg_idents(self.local_def_id.to_def_id())
            .iter()
            .map(|ident| {
                ident
                    .expect("predicate arguments must be named")
                    .name
                    .to_string()
            });

        let sig = self
            .ctx
            .fn_sig_with_body(self.local_def_id.to_def_id(), &self.body);
        let arg_sorts = sig
            .inputs()
            .iter()
            .map(|input_ty| self.type_builder.build(*input_ty).to_sort());

        let arg_name_and_sorts = arg_names.into_iter().zip(arg_sorts).collect::<Vec<_>>();

        (
            chc::UserDefinedPredSig::from(arg_name_and_sorts),
            predicate_body,
        )
    }

    /// Whether the def comes from the injected `std.rs`. The bodies there are the specification
    /// library's own proofs, such as the laws its impls prove; they are checked once, by compiling
    /// `std.rs` as an ordinary source file, rather than again in every crate.
    pub fn is_injected_std(&self) -> bool {
        analyze::is_injected_std(self.tcx, self.local_def_id)
    }

    pub fn is_annotated_as_trusted(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::trusted_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_callable(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::callable_path(),
            )
            .next()
            .is_some()
    }

    /// Whether the def is the `drop` method of a `Drop` impl. Rust runs it wherever a value of the
    /// type is dropped, also in code Thrust does not analyze, so as in Verus it takes no
    /// precondition: it is checked under `requires(true)`, and no drop can panic.
    pub fn is_crate_destructor(&self) -> bool {
        let Some(impl_def_id) = self.tcx.impl_of_assoc(self.local_def_id.to_def_id()) else {
            return false;
        };
        self.tcx.trait_id_of_impl(impl_def_id) == self.tcx.lang_items().drop_trait()
    }

    /// Whether the def carries a written contract: a `requires` or an `ensures` (also through
    /// `#[thrust::callable]`), or a refinement of a parameter or of the result (`param`, `ret`,
    /// `sig`).
    pub fn has_contract_annotation(&self) -> bool {
        let has_path = |path: &[rustc_span::Symbol]| {
            self.ctx
                .extract_path_with_attr(self.local_def_id, path)
                .is_some()
        };
        self.is_annotated_as_callable()
            || has_path(&analyze::annot::requires_path_path())
            || has_path(&analyze::annot::ensures_path_path())
            || !self
                .ctx
                .extract_refinement_paths(self.local_def_id)
                .is_empty()
    }

    pub fn is_annotated_as_extern_spec_fn(&self) -> bool {
        is_annotated_as_extern_spec_fn_impl(&self.tcx, &self.local_def_id)
    }

    pub fn is_annotated_as_predicate(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::predicate_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_annotated_as_ignored(&self) -> bool {
        analyze::is_ignored(self.tcx, self.local_def_id.to_def_id())
    }

    pub fn is_ignored_derive(&self) -> bool {
        analyze::derive::is_ignored(self.tcx, self.local_def_id.to_def_id())
    }

    pub fn is_trusted_derive(&self) -> bool {
        analyze::derive::is_trusted(
            self.tcx,
            &self.ctx.def_ids(),
            &self.type_builder,
            self.local_def_id.to_def_id(),
        )
    }

    /// A trusted derive's contract holds only where the impls of its trait at the fields' types
    /// meet the trait's specification ([`analyze::Analyzer::check_bound_impls`]).
    pub fn check_derived_field_impls(&self) {
        let def_id = self.local_def_id.to_def_id();
        let typing_env = mir_ty::TypingEnv::post_analysis(self.tcx, def_id);
        let bounds = analyze::derive::field_bounds(self.tcx, def_id);
        self.ctx.check_bound_impls(def_id, typing_env, bounds);
    }

    pub fn is_annotated_as_formula_fn(&self) -> bool {
        self.tcx
            .get_attrs_by_path(
                self.local_def_id.to_def_id(),
                &analyze::annot::formula_fn_path(),
            )
            .next()
            .is_some()
    }

    pub fn is_fully_annotated(&self) -> bool {
        let has_requires = self
            .ctx
            .extract_path_with_attr(self.local_def_id, &analyze::annot::requires_path_path())
            .is_some();
        let has_ensures = self
            .ctx
            .extract_path_with_attr(self.local_def_id, &analyze::annot::ensures_path_path())
            .is_some();

        self.is_annotated_as_callable() || (has_requires && has_ensures)
    }

    pub fn local_trait_item_id(&self) -> Option<LocalDefId> {
        let impl_item_assoc = self
            .tcx
            .opt_associated_item(self.local_def_id.to_def_id())?;
        let trait_item_id = impl_item_assoc
            .trait_item_def_id
            .and_then(|id| id.as_local())?;

        if trait_item_id == self.local_def_id {
            return None;
        }

        Some(trait_item_id)
    }

    /// The generic arguments the implemented trait method takes for the instantiation
    /// being analyzed.
    pub fn trait_item_args(&self) -> Option<mir_ty::GenericArgsRef<'tcx>> {
        let impl_did = self.tcx.parent(self.local_def_id.to_def_id());

        if self.tcx.def_kind(impl_did) != (rustc_hir::def::DefKind::Impl { of_trait: true }) {
            return None;
        }

        // an associated method's generic arguments start with those of its impl
        let trait_ref = self
            .tcx
            .impl_trait_ref(impl_did)?
            .instantiate(self.tcx, self.generic_args);
        // ... and end with the method's own, which the trait method is generic over as well
        let own_args = self
            .generic_args
            .iter()
            .skip(self.tcx.generics_of(self.local_def_id).parent_count);
        Some(
            self.tcx
                .mk_args_from_iter(trait_ref.args.iter().chain(own_args)),
        )
    }

    pub fn trait_item_ty(&mut self) -> Option<rty::RefinedType> {
        let trait_item_args = self.trait_item_args()?;
        let trait_item_did = self
            .tcx
            .associated_item(self.local_def_id.to_def_id())
            .trait_item_def_id
            .unwrap();
        // The trait method's type must be built under this analysis's actual owner
        // (`self.owner_fn_id`), not under the impl item itself: when the impl item is
        // being re-analyzed as a generic callee (`Analyzer::def_ty_with_args`'s `Analyze`
        // mode, for a call whose type arguments are the caller's own type parameters),
        // `owner_fn_id` has been overridden to the caller so this contract is typed over
        // the caller's abstract sorts. Passing `local_def_id` here instead reintroduces
        // the impl item's own, independently-numbered sorts, which then disagree with
        // the sorts the rest of `expected_ty` (and the caller's own translation of the
        // call) used for the same type parameter.
        self.ctx
            .def_ty_with_args(trait_item_did, trait_item_args, self.owner_fn_id)
    }

    // TODO: Remove this eager precompute together with
    // `Analyzer::known_function_ty_with_args` once formula translation can call a read-only
    // `def_ty_with_args` directly.
    fn precompute_callable_param_contracts(&mut self, sig: &mir_ty::FnSig<'tcx>) {
        for input_ty in sig.inputs() {
            let inst = self
                .tcx
                .try_normalize_erasing_regions(mir_ty::TypingEnv::fully_monomorphized(), *input_ty)
                .unwrap_or(*input_ty);

            // Eagerly register closure type parameters (e.g. `F: Fn(...)` declared on
            // this function) so that basic-block analysis can look up the contract
            // when it later sees `<F as Fn<...>>::call(...)`.
            let param_ty = match inst.kind() {
                mir_ty::TyKind::Param(p) => Some(*p),
                mir_ty::TyKind::Ref(_, inner, _) => {
                    if let mir_ty::TyKind::Param(p) = inner.kind() {
                        Some(*p)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            // No resolution here: `sig` comes from the body, which `Self::generic_args`
            // has already instantiated, so `param_ty` is a parameter of the caller
            // already -- applying the arguments a second time would be out of range.
            if let Some(param_ty) = param_ty {
                if let Some(fun_ty) = self.type_builder.build_closure_type_for_param(
                    param_ty,
                    self.local_def_id,
                    self.tcx.mk_args(&[]),
                ) {
                    self.type_builder.register_closure_type_param(
                        analyze::TypeParam::GenericType {
                            param_def_id: self.type_builder.param_def_id(&param_ty),
                            local_idx: self.type_builder.param_local_idx(&param_ty),
                        },
                        fun_ty,
                    );
                }
            }

            // A callable passed by reference (`g: &mut G` at a closure) is looked up the same way.
            let callable = match inst.kind() {
                mir_ty::TyKind::Ref(_, inner, _) => *inner,
                _ => inst,
            };
            let (fn_def_id, fn_args) = match callable.kind() {
                mir_ty::TyKind::Closure(def_id, args) => {
                    (*def_id, self.tcx.mk_args(args.as_closure().parent_args()))
                }
                mir_ty::TyKind::FnDef(def_id, args) => (*def_id, *args),
                _ => continue,
            };
            if fn_def_id == self.local_def_id.to_def_id() {
                continue;
            }
            let _ = self
                .ctx
                .def_ty_with_args(fn_def_id, fn_args, self.owner_fn_id);
        }

        let parent_def_id = self.tcx.parent(self.local_def_id.to_def_id());
        if matches!(
            self.tcx.def_kind(parent_def_id),
            rustc_hir::def::DefKind::Impl { .. }
        ) {
            if let Some(impl_local_def_id) = parent_def_id.as_local() {
                self.precompute_impl_closure_type_params(impl_local_def_id);
            }
        }
    }

    /// Analyses, at this analysis's arguments, the functions this def's contract names by path
    /// in `pre!`/`post!` (`<F as Deref>::deref` at `F` instantiated), so that the translation
    /// finds their contracts as it finds a callable parameter's.
    fn precompute_named_fn_contracts(&mut self) {
        use mir_ty::TypeVisitableExt as _;

        let def_ids = self.ctx.def_ids();
        let markers = [
            def_ids.closure_precondition(),
            def_ids.closure_postcondition(),
        ];
        let formula_fns: Vec<_> = [
            analyze::annot::requires_path_path(),
            analyze::annot::ensures_path_path(),
        ]
        .iter()
        .filter_map(|path| self.ctx.extract_path_with_attr(self.local_def_id, path))
        .filter_map(|def_id| def_id.as_local())
        .collect();
        for formula_fn in formula_fns {
            let typeck = self.tcx.typeck(formula_fn);
            let named: Vec<_> = typeck
                .node_types()
                .items_in_stable_order()
                .into_iter()
                .filter_map(|(_, ty)| match ty.kind() {
                    mir_ty::TyKind::FnDef(marker, args) if markers.contains(&Some(*marker)) => {
                        match args.type_at(0).kind() {
                            mir_ty::TyKind::FnDef(def_id, args) => Some((*def_id, *args)),
                            _ => None,
                        }
                    }
                    _ => None,
                })
                .collect();
            for (def_id, args) in named {
                let args = if self.generic_args.is_empty() {
                    args
                } else {
                    mir_ty::EarlyBinder::bind(args).instantiate(self.tcx, self.generic_args)
                };
                // Resolved as the translation resolves it (`annot_fn`'s `fn_item_contract`):
                // under the owner's bounds, so that an impl applying whatever the owner's type
                // parameters are, such as the reflexive `From`, is found at arguments naming them.
                let typing_env =
                    analyze::predicate_typing_env(self.tcx, self.owner_fn_id, def_ids.model_ty());
                let Ok(Some(instance)) =
                    mir_ty::Instance::try_resolve(self.tcx, typing_env, def_id, args)
                else {
                    if args.has_param() {
                        // A trait-level spec, as a call at the type parameters takes.
                        let _ = self.ctx.def_ty_with_args(def_id, args, self.owner_fn_id);
                    }
                    continue;
                };
                if instance.def_id() != self.local_def_id.to_def_id() {
                    let _ = self.ctx.def_ty_with_args(
                        instance.def_id(),
                        instance.args,
                        self.owner_fn_id,
                    );
                }
            }
        }
    }

    /// Walks `impl_local_def_id`'s `predicates_of` and registers any
    /// `Fn`/`FnMut`/`FnOnce` type parameters declared on the impl.
    fn precompute_impl_closure_type_params(&mut self, impl_local_def_id: LocalDefId) {
        for (clause, _) in self
            .tcx
            .predicates_of(impl_local_def_id.to_def_id())
            .predicates
            .iter()
        {
            let Some(trait_clause) = clause.as_trait_clause() else {
                continue;
            };
            let trait_ref = trait_clause.skip_binder();
            if self
                .tcx
                .fn_trait_kind_from_def_id(trait_ref.def_id())
                .is_none()
            {
                continue;
            }
            let mir_ty::TyKind::Param(p) = trait_ref.self_ty().kind() else {
                continue;
            };
            // `p` is declared by the impl block. Only the parameter this analysis's
            // arguments map it to lives in the index space `param_local_idx` reads.
            let Some(p) = self.type_builder.resolve_param_ty(*p, self.generic_args) else {
                continue;
            };
            if let Some(fun_ty) = self.type_builder.build_closure_type_for_param(
                p,
                impl_local_def_id,
                self.generic_args,
            ) {
                self.type_builder.register_closure_type_param(
                    analyze::TypeParam::GenericType {
                        param_def_id: self.type_builder.param_def_id(&p),
                        local_idx: self.type_builder.param_local_idx(&p),
                    },
                    fun_ty,
                );
            }
        }
    }

    // Note that we do not expect predicate variables to be generated here
    // when type params are still present in the type. Callers should ensure either
    // - type params are fully instantiated, or
    // - the function is fully annotated
    pub fn expected_ty(&mut self) -> rty::RefinedType {
        let sig = self
            .ctx
            .fn_sig_with_body(self.local_def_id.to_def_id(), &self.body);

        // Formula translation for `pre!(f(..))`/`post!(f(..), result)` is read-only. If a callable
        // parameter resolves to a deferred closure/function def, force its analysis here so the
        // translator can later find the cached contract.
        self.precompute_callable_param_contracts(&sig);
        self.precompute_named_fn_contracts();

        let mut require_annot =
            self.ctx
                .extract_require_annot(self.local_def_id, self.generic_args, self.owner_fn_id);
        let mut ensure_annot =
            self.ctx
                .extract_ensure_annot(self.local_def_id, self.generic_args, self.owner_fn_id);

        if let Some((trait_item_id, trait_item_args)) =
            self.local_trait_item_id().zip(self.trait_item_args())
        {
            tracing::info!("trait item found: {:?}", trait_item_id);
            let trait_require_annot =
                self.ctx
                    .extract_require_annot(trait_item_id, trait_item_args, self.owner_fn_id);
            let trait_ensure_annot =
                self.ctx
                    .extract_ensure_annot(trait_item_id, trait_item_args, self.owner_fn_id);

            assert!(require_annot.is_none() || trait_require_annot.is_none());
            require_annot = require_annot.or(trait_require_annot);

            assert!(ensure_annot.is_none() || trait_ensure_annot.is_none());
            ensure_annot = ensure_annot.or(trait_ensure_annot);
        }

        let refinement_annots = self.ctx.extract_refinement_annots(
            self.local_def_id,
            self.generic_args,
            self.owner_fn_id,
        );
        let annotations = self.ctx.contract_annotations(
            require_annot.as_ref().map(|(def_id, _)| *def_id),
            ensure_annot.as_ref().map(|(def_id, _)| *def_id),
            refinement_annots
                .iter()
                .map(|(position, def_id, _)| (position.clone(), *def_id)),
        );
        let annotated = if self.is_annotated_as_extern_spec_fn() {
            self.extern_spec_fn_target_def_id()
        } else {
            self.local_def_id.to_def_id()
        };
        self.ctx.record_contract_annotations(annotated, annotations);
        let mut require_annot = require_annot.map(|(_, formula)| formula);
        let mut ensure_annot = ensure_annot.map(|(_, formula)| formula);

        if self.is_annotated_as_callable() {
            assert!(require_annot.is_none() && ensure_annot.is_none());
            require_annot = Some(chc::Formula::top());
            ensure_annot = Some(chc::Formula::top());
        }
        if self.is_crate_destructor() {
            require_annot = Some(chc::Formula::top());
        }

        let trait_item_ty = self.trait_item_ty();
        let is_fully_annotated = self.is_fully_annotated();
        let is_callable = self.is_annotated_as_callable();

        let mut builder = self.type_builder.for_function_template(&mut self.ctx, sig);
        if let Some(require) = require_annot {
            let formula = require.map_var(|idx| {
                if idx.index() == sig.inputs().len() - 1 {
                    rty::RefinedTypeVar::Value
                } else {
                    rty::RefinedTypeVar::Free(idx)
                }
            });
            builder.param_refinement(formula.into());
        }
        if let Some(ensure) = ensure_annot {
            builder.ret_refinement(ensure.into());
        }
        for (position, _, refinement) in refinement_annots {
            builder.refinement_at(&position, refinement);
        }

        // A call resolved to the method takes the trait's contract, so `callable` does not weaken
        // what its body is checked against.
        if !is_fully_annotated || is_callable {
            if let Some(trait_item_ty) = trait_item_ty {
                return trait_item_ty;
            }
        }
        let mut fn_ty = builder.build();
        self.conjoin_fn_mut_hist_inv(&mut fn_ty);
        self.conjoin_type_invariants(sig, &mut fn_ty);
        rty::RefinedType::unrefined(fn_ty.into())
    }

    /// Conjoins the type invariants of the parameters and the result to the contract, as
    /// Creusot's `Invariant` does (`creusot/src/backend/ty_inv.rs`, `sig_add_type_invariant_spec`):
    /// a parameter of a type `T` with an `Invariant` impl in std.rs's sense, or a `&T` or
    /// `&mut T` to one, requires `T::invariant` of its value (the current value of a reference);
    /// a `&mut T` parameter also ensures it of its final value; a result of such a type, or a
    /// reference to one, ensures it of its (current) value. Since the invariant becomes a
    /// conjunct of the contract, the body is checked against it at its exits and every caller
    /// proves it at the call, as for a written `requires`/`ensures`; a function's body may break
    /// it between those points. It is not assumed of the final value of a returned `&mut`, which
    /// the caller sets: unlike Creusot, Thrust does not check the invariant where a borrow is
    /// resolved. `#[thrust::open_inv]` on a parameter and `#[thrust::open_inv_result]` on the
    /// function leave theirs out. Closures, lemmas and laws get none, and a type parameter, whose
    /// `Invariant` impl does not resolve, has none.
    fn conjoin_type_invariants(&mut self, sig: mir_ty::FnSig<'tcx>, fn_ty: &mut rty::FunctionType) {
        if self.ctx.def_ids.type_invariant().is_none()
            || self.tcx.is_closure_like(self.local_def_id.to_def_id())
            || self.has_attr(&analyze::annot::lemma_path())
            || self.has_attr(&analyze::annot::law_path())
        {
            return;
        }
        let open_params = self.open_inv_params();
        let last = sig.inputs().len().wrapping_sub(1);
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        for (idx, ty) in sig.inputs().iter().enumerate() {
            if open_params.contains(&idx) {
                continue;
            }
            let param_idx = rty::FunctionParamIdx::from_usize(idx);
            let at_entry = if idx == last {
                chc::Term::var(rty::RefinedTypeVar::Value)
            } else {
                chc::Term::var(rty::RefinedTypeVar::Free(param_idx))
            };
            match ty.kind() {
                mir_ty::TyKind::Ref(_, inner, mir_ty::Mutability::Mut) => {
                    let Some(pred) = self.type_invariant_pred(*inner) else {
                        continue;
                    };
                    requires.push(type_invariant_atom(&pred, at_entry.mut_current()));
                    let at_exit = chc::Term::var(rty::RefinedTypeVar::Free(param_idx));
                    ensures.push(type_invariant_atom(&pred, at_exit.mut_final()));
                }
                mir_ty::TyKind::Ref(_, inner, mir_ty::Mutability::Not) => {
                    if let Some(pred) = self.type_invariant_pred(*inner) {
                        requires.push(type_invariant_atom(&pred, at_entry.box_current()));
                    }
                }
                _ => {
                    if let Some(pred) = self.type_invariant_pred(*ty) {
                        requires.push(type_invariant_atom(&pred, at_entry));
                    }
                }
            }
        }
        if !self.has_attr(&analyze::annot::open_inv_result_path()) {
            let result = chc::Term::var(rty::RefinedTypeVar::Value);
            let ret = sig.output();
            let (ty, term) = match ret.kind() {
                mir_ty::TyKind::Ref(_, inner, mir_ty::Mutability::Mut) => {
                    (*inner, result.mut_current())
                }
                mir_ty::TyKind::Ref(_, inner, mir_ty::Mutability::Not) => {
                    (*inner, result.box_current())
                }
                _ => (ret, result),
            };
            if let Some(pred) = self.type_invariant_pred(ty) {
                ensures.push(type_invariant_atom(&pred, term));
            }
        }
        if let Some(last_idx) = fn_ty.params.last_index() {
            for formula in requires {
                fn_ty.params[last_idx].extend_refinement(formula.into());
            }
        }
        for formula in ensures {
            fn_ty.ret.extend_refinement(formula.into());
        }
    }

    /// The predicate `T::invariant` of std.rs's `Invariant` at `ty`, when its impl resolves in the
    /// owner's environment.
    fn type_invariant_pred(&self, ty: mir_ty::Ty<'tcx>) -> Option<chc::Pred> {
        let trait_did = self.ctx.def_ids.type_invariant()?;
        let inv_did = *self.tcx.associated_item_def_ids(trait_did).first()?;
        if self.type_builder.build(ty).ty.to_sort().is_singleton() {
            return None;
        }
        let typing_env =
            analyze::predicate_typing_env(self.tcx, self.owner_fn_id, self.ctx.def_ids.model_ty());
        let args = self.tcx.mk_args(&[ty.into()]);
        let instance = mir_ty::Instance::try_resolve(self.tcx, typing_env, inv_did, args)
            .ok()
            .flatten()?;
        if instance.def_id() == inv_did {
            return None;
        }
        Some(
            self.ctx
                .predicate_with_args(instance.def_id(), instance.args, self.owner_fn_id)
                .into(),
        )
    }

    /// The indices of the parameters marked `#[thrust::open_inv]`.
    fn open_inv_params(&self) -> HashSet<usize> {
        let path = analyze::annot::open_inv_path();
        let mut open = HashSet::new();
        for local_def_id in self.attributed_defs() {
            let Some(body) = self.tcx.hir_maybe_body_owned_by(local_def_id) else {
                continue;
            };
            for (idx, param) in body.params.iter().enumerate() {
                if self
                    .tcx
                    .hir_attrs(param.hir_id)
                    .iter()
                    .any(|attr| attr.path_matches(&path))
                {
                    open.insert(idx);
                }
            }
        }
        open
    }

    /// The defs whose attributes apply to this def's contract: the def, and the local function
    /// an extern spec specifies (the one `requires`/`ensures` generate for a local function).
    fn attributed_defs(&self) -> Vec<LocalDefId> {
        let mut defs = vec![self.local_def_id];
        if self.is_annotated_as_extern_spec_fn() {
            if let Some(target) = self.extern_spec_fn_target_def_id().as_local() {
                defs.push(target);
            }
        }
        defs
    }

    fn has_attr(&self, path: &[rustc_span::Symbol]) -> bool {
        self.attributed_defs().into_iter().any(|def| {
            self.tcx
                .get_attrs_by_path(def.to_def_id(), path)
                .next()
                .is_some()
        })
    }

    /// Conjoins to an `FnMut` closure's postcondition that the call keeps the closure's state
    /// related by `hist_inv!` (each `&mut` capture keeps its prophecy, each `&` capture its value),
    /// as Creusot's `postcondition_mut` of a closure includes `hist_inv(self, ^self)`. The body
    /// is checked against it, and it makes the law that each call's postcondition implies
    /// `hist_inv!` hold of every such closure's contract.
    fn conjoin_fn_mut_hist_inv(&self, fn_ty: &mut rty::FunctionType) {
        if !self.tcx.is_closure_like(self.local_def_id.to_def_id()) {
            return;
        }
        let closure_ty = self.tcx.type_of(self.local_def_id).instantiate_identity();
        let mir_ty::TyKind::Closure(_, args) = closure_ty.kind() else {
            return;
        };
        if args.as_closure().kind() != mir_ty::ClosureKind::FnMut {
            return;
        }
        let receiver = &fn_ty.params[rty::FunctionParamIdx::from_usize(0)].ty;
        if receiver.as_pointer().map(|ty| ty.kind) != Some(rty::PointerKind::Ref(rty::RefKind::Mut))
        {
            return;
        }
        let upvars_sort = receiver.to_sort().deref();
        let receiver = chc::Term::var(rty::RefinedTypeVar::Free(
            rty::FunctionParamIdx::from_usize(0),
        ));
        let formula = self.ctx.closure_hist_inv_definition(
            closure_ty,
            &upvars_sort,
            receiver.clone().mut_current(),
            receiver.mut_final(),
        );
        if formula.is_top() {
            return;
        }
        fn_ty.ret.extend_refinement(formula.into());
    }

    /// Extract the target DefId from `#[thrust::extern_spec_fn]` function.
    ///
    /// The target is identified as the tail call expression (last expression without
    /// semicolon) in the function body block.
    pub fn extern_spec_fn_target_def_id(&self) -> DefId {
        extern_spec_fn_target_def_id_impl(&self.tcx, &self.local_def_id, &self.body).0
    }

    fn is_mut_param(&self, param_idx: rty::FunctionParamIdx) -> bool {
        let param_local = analyze::local_of_function_param(param_idx);
        self.body.local_decls[param_local].mutability.is_mut()
    }

    fn extract_elaborated_deref(
        &self,
        stmt: &mir::Statement<'tcx>,
    ) -> Option<(Local, mir::Place<'tcx>)> {
        let mir::StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        let (lhs, rvalue) = &**assign;
        if !lhs.projection.as_ref().is_empty() {
            return None;
        }
        let lhs_local = lhs.local;

        if let mir::Rvalue::CopyForDeref(place) = &rvalue {
            return Some((lhs_local, *place));
        }

        let unique_did = self.ctx.def_ids.unique()?;
        let nonnull_did = self.ctx.def_ids.nonnull()?;

        use mir::ProjectionElem::Field;
        use rustc_abi::FieldIdx;
        const ZERO_FIELD: FieldIdx = FieldIdx::from_u32(0);

        // Box deref pattern: `(_box.0.0 as *const T) Transmute`
        //   projection = [..., Field(0, Unique<T>), Field(0, NonNull<T>)], transmuted to *const T
        let mir::Rvalue::Cast(mir::CastKind::Transmute, mir::Operand::Copy(place), cast_ty) =
            &rvalue
        else {
            return None;
        };
        if !matches!(cast_ty.kind(), mir_ty::TyKind::RawPtr(_, mutbl) if mutbl.is_not()) {
            return None;
        }
        let Some((rest, [Field(ZERO_FIELD, ty0), Field(ZERO_FIELD, ty1)])) =
            place.projection.as_slice().split_last_chunk::<2>()
        else {
            return None;
        };
        let rest_place = mir::Place {
            local: place.local,
            projection: self.tcx.mk_place_elems(rest),
        };
        let local_ty = rest_place.ty(&self.body.local_decls, self.tcx).ty;
        if !local_ty.is_box() {
            return None;
        }
        let inner_ty = local_ty.boxed_ty()?;
        if !matches!(ty0.kind(), mir_ty::TyKind::Adt(def, args)
            if def.did() == unique_did && args.type_at(0) == inner_ty)
        {
            return None;
        }
        if !matches!(ty1.kind(), mir_ty::TyKind::Adt(def, args)
            if def.did() == nonnull_did && args.type_at(0) == inner_ty)
        {
            return None;
        }
        Some((lhs_local, rest_place))
    }

    /// Replaces each temporary that copies a pointer for a deref (`CopyForDeref`, and the
    /// transmuted pointer of a `Box`) with the place it copies, unless that place may change
    /// between the copy and a use of the temporary. Optimizations make that possible: a
    /// reborrow `q = &mut *_k` becomes `q = copy _k` and `q` is merged into `_k`.
    fn unelaborate_derefs(&mut self) {
        let original = self.body.clone();
        let replaced = self.replace_deref_temps(&HashSet::new());
        let kept = self.deref_temps_read_after_change(&original, &replaced);
        if kept.is_empty() {
            return;
        }
        self.body = original;
        self.replace_deref_temps(&kept);
    }

    /// Replaces the deref temporaries other than `kept`, each kept one becoming a copy of its
    /// place, and returns the replaced ones with their definitions and places.
    fn replace_deref_temps(
        &mut self,
        kept: &HashSet<Local>,
    ) -> Vec<(Local, mir::Location, mir::Place<'tcx>)> {
        let mut replaced = Vec::new();
        let mut v = analyze::ReplacePlacesVisitor::new(self.tcx);
        for (block, data) in self.body.basic_blocks.clone().iter_enumerated() {
            for (idx, _stmt) in data.statements.iter().enumerate() {
                let stmt =
                    &mut self.body.basic_blocks.as_mut().as_mut_slice()[block].statements[idx];
                v.visit_statement(stmt);
                let stmt = stmt.clone();
                let Some((dest_local, place)) = self.extract_elaborated_deref(&stmt) else {
                    continue;
                };
                let kind = if kept.contains(&dest_local) {
                    kept_deref_temp(&stmt, dest_local, place)
                } else {
                    v.add_replacement(dest_local.into(), place);
                    let def = mir::Location {
                        block,
                        statement_index: idx,
                    };
                    replaced.push((dest_local, def, place));
                    mir::StatementKind::Nop
                };
                self.body.basic_blocks.as_mut().as_mut_slice()[block].statements[idx].kind = kind;
            }
            if let Some(tmnt) =
                &mut self.body.basic_blocks.as_mut().as_mut_slice()[block].terminator
            {
                v.visit_terminator(tmnt);
            }
        }
        replaced
    }

    /// The deref temporaries of `replaced` whose place may be written, in `self.body` where
    /// every one is replaced, between the copy and a use: a use of `original`'s temporary, or
    /// a use of a temporary copied through it.
    fn deref_temps_read_after_change(
        &self,
        original: &Body<'tcx>,
        replaced: &[(Local, mir::Location, mir::Place<'tcx>)],
    ) -> HashSet<Local> {
        let mut uses = local_mentions(original);
        let mut defs: HashMap<Local, Vec<mir::Location>> = HashMap::new();
        for (temp, def, _) in replaced {
            defs.entry(*temp).or_default().push(*def);
        }
        for (temp, def, _) in replaced {
            uses.entry(*temp).or_default().retain(|loc| loc != def);
        }
        let uses = with_uses_through_copies(uses, replaced);
        let mentions = local_mentions(&self.body);
        let mut kept = HashSet::new();
        for (temp, def, place) in replaced {
            if defs[temp].len() != 1
                || self.has_unknown_aliases(place)
                || self.written_before_use(place, *def, &uses[temp], &mentions)
            {
                kept.insert(*temp);
            }
        }
        kept
    }

    fn has_unknown_aliases(&self, place: &mir::Place<'tcx>) -> bool {
        place.iter_projections().any(|(base, elem)| match elem {
            mir::ProjectionElem::Deref => base.ty(&self.body.local_decls, self.tcx).ty.is_raw_ptr(),
            mir::ProjectionElem::Index(_) => true,
            _ => false,
        })
    }

    /// Whether a use in `uses` can be reached without passing `def` from a change of `place`:
    /// a write, or a use of an alias that may write it.
    fn written_before_use(
        &self,
        place: &mir::Place<'tcx>,
        def: mir::Location,
        uses: &[mir::Location],
        mentions: &HashMap<Local, Vec<mir::Location>>,
    ) -> bool {
        let uses: HashSet<_> = uses.iter().copied().collect();
        let (mut changes, aliases) = self.changes_of(place);
        for local in self.alias_locals(&aliases, mentions) {
            changes.extend(mentions[&local].iter().copied());
        }
        changes.extend(aliases);
        self.reaches_any(&changes, def, &uses)
    }

    /// The locals assigned from the aliases made at `aliases`, and from those locals.
    fn alias_locals(
        &self,
        aliases: &[mir::Location],
        mentions: &HashMap<Local, Vec<mir::Location>>,
    ) -> HashSet<Local> {
        let mut pending: Vec<_> = aliases
            .iter()
            .filter_map(|loc| self.assigned_local(*loc))
            .collect();
        let mut locals = HashSet::new();
        while let Some(local) = pending.pop() {
            if !locals.insert(local) {
                continue;
            }
            let assigned = mentions[&local]
                .iter()
                .filter_map(|loc| self.assigned_local(*loc));
            pending.extend(assigned.filter(|assigned| *assigned != local));
        }
        locals
    }

    fn assigned_local(&self, loc: mir::Location) -> Option<Local> {
        let data = &self.body.basic_blocks[loc.block];
        let Some(stmt) = data.statements.get(loc.statement_index) else {
            let mir::TerminatorKind::Call { destination, .. } = &data.terminator().kind else {
                return None;
            };
            return Some(destination.local);
        };
        let mir::StatementKind::Assign(assign) = &stmt.kind else {
            return None;
        };
        Some(assign.0.local)
    }

    fn reaches_any(
        &self,
        from: &[mir::Location],
        barrier: mir::Location,
        targets: &HashSet<mir::Location>,
    ) -> bool {
        let mut stack: Vec<_> = from
            .iter()
            .flat_map(|loc| location_successors(&self.body, *loc))
            .collect();
        let mut seen = HashSet::new();
        while let Some(loc) = stack.pop() {
            if loc == barrier || !seen.insert(loc) {
                continue;
            }
            if targets.contains(&loc) {
                return true;
            }
            stack.extend(location_successors(&self.body, loc));
        }
        false
    }

    /// The locations that may change the value at `place`: writes to and moves out of a place
    /// it is read through, and the aliases of such a place that may write it, a mutable or raw
    /// borrow or a copy of a non-`Copy` value such as a `&mut` it is reached through.
    fn changes_of(&self, place: &mir::Place<'tcx>) -> (Vec<mir::Location>, Vec<mir::Location>) {
        use mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext};
        struct Visitor<'a, 'tcx> {
            analyzer: &'a Analyzer<'tcx, 'a>,
            place: &'a mir::Place<'tcx>,
            writes: Vec<mir::Location>,
            aliases: Vec<mir::Location>,
        }
        impl<'tcx> mir::visit::Visitor<'tcx> for Visitor<'_, 'tcx> {
            fn visit_place(
                &mut self,
                other: &mir::Place<'tcx>,
                context: PlaceContext,
                location: mir::Location,
            ) {
                if other.local != self.place.local
                    || !self.analyzer.changes_place(other, self.place)
                {
                    return;
                }
                match context {
                    PlaceContext::MutatingUse(
                        MutatingUseContext::Borrow | MutatingUseContext::RawBorrow,
                    )
                    | PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow) => {
                        self.aliases.push(location)
                    }
                    PlaceContext::NonMutatingUse(
                        NonMutatingUseContext::Copy | NonMutatingUseContext::Move,
                    ) if other.projection.len() < self.place.projection.len()
                        && !self.analyzer.is_copy(other) =>
                    {
                        self.aliases.push(location)
                    }
                    PlaceContext::MutatingUse(_)
                    | PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                        self.writes.push(location)
                    }
                    _ => {}
                }
            }
        }
        let mut visitor = Visitor {
            analyzer: self,
            place,
            writes: Vec::new(),
            aliases: Vec::new(),
        };
        mir::visit::Visitor::visit_body(&mut visitor, &self.body);
        (visitor.writes, visitor.aliases)
    }

    /// Whether writing `written`, of the local of `place`, may change the value read at
    /// `place`: it does unless it is a disjoint field or is reached through a pointer `place`
    /// holds.
    fn changes_place(&self, written: &mir::Place<'tcx>, place: &mir::Place<'tcx>) -> bool {
        let common = written.projection.len().min(place.projection.len());
        for i in 0..common {
            let (ew, ep) = (written.projection[i], place.projection[i]);
            if ew == ep {
                continue;
            }
            let base = mir::PlaceRef {
                local: place.local,
                projection: &place.projection[..i],
            };
            let is_union = base.ty(&self.body.local_decls, self.tcx).ty.is_union();
            return match (ew, ep) {
                (mir::ProjectionElem::Field(fw, _), mir::ProjectionElem::Field(fp, _)) => {
                    fw == fp || is_union
                }
                _ => true,
            };
        }
        written.projection.get(common) != Some(&mir::ProjectionElem::Deref)
    }

    fn is_copy(&self, place: &mir::Place<'tcx>) -> bool {
        let ty = place.ty(&self.body.local_decls, self.tcx).ty;
        self.tcx
            .type_is_copy_modulo_regions(self.analysis_key().typing_env(self.tcx), ty)
    }

    fn mut_locals(
        &self,
        data: &mir::BasicBlockData<'tcx>,
        statement_index: usize,
    ) -> DenseBitSet<Local> {
        struct Visitor<'tcx, 'a> {
            tcx: TyCtxt<'tcx>,
            typing_env: mir_ty::TypingEnv<'tcx>,
            body: &'a Body<'tcx>,

            locals: DenseBitSet<Local>,
        }
        impl<'tcx> mir::visit::Visitor<'tcx> for Visitor<'tcx, '_> {
            fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
                if let mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place) = rvalue {
                    self.locals.insert(place.local);
                }
                self.super_rvalue(rvalue, location);
            }

            fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, location: mir::Location) {
                // to be reborrowed; see analyze::basic_block::visitor. A `&mut`
                // field read out of an aggregate is `copy (_1.0)`, so match Copy
                // too to mark the base local. Reference only: `is_mutable_ptr()`
                // also covers `*mut`, which is Copy but never reborrowed.
                if let mir::Operand::Move(place) | mir::Operand::Copy(place) = operand {
                    if matches!(
                        place.ty(&self.body.local_decls, self.tcx).ty.kind(),
                        mir_ty::TyKind::Ref(_, _, m) if m.is_mut()
                    ) {
                        self.locals.insert(place.local);
                    }
                }
                self.super_operand(operand, location);
            }

            fn visit_terminator(
                &mut self,
                terminator: &mir::Terminator<'tcx>,
                location: mir::Location,
            ) {
                // a destructor of the crate is called with `&mut` of the dropped place; see
                // analyze::basic_block::Analyzer::call_destructors
                if let mir::TerminatorKind::Drop { place, .. } = &terminator.kind {
                    let ty = place.ty(&self.body.local_decls, self.tcx).ty;
                    if analyze::drop_runs_local_destructor(self.tcx, self.typing_env, ty) {
                        self.locals.insert(place.local);
                    }
                }
                // calling an FnMut closure via FnOnce::call_once resolves to the closure
                // function taking &mut {closure}, so RustCallVisitor mutably borrows the
                // closure argument; see analyze::basic_block::visitor
                if let mir::TerminatorKind::Call { func, args, .. } = &terminator.kind {
                    if let Some((def_id, generic_args)) = func.const_fn_def() {
                        let trait_did = self
                            .tcx
                            .opt_associated_item(def_id)
                            .and_then(|item| item.trait_container(self.tcx));
                        if trait_did.is_some() && trait_did == self.tcx.lang_items().fn_once_trait()
                        {
                            if let mir_ty::TyKind::Closure(_, closure_args) =
                                generic_args.type_at(0).kind()
                            {
                                if closure_args.as_closure().kind() == mir_ty::ClosureKind::FnMut {
                                    if let Some(place) = args[0].node.place() {
                                        self.locals.insert(place.local);
                                    }
                                }
                            }
                        }
                    }
                }
                self.super_terminator(terminator, location);
            }

            fn visit_assign(
                &mut self,
                place: &mir::Place<'tcx>,
                rvalue: &mir::Rvalue<'tcx>,
                location: mir::Location,
            ) {
                self.locals.insert(place.local);
                self.super_assign(place, rvalue, location);
            }
        }

        let mut visitor = Visitor {
            tcx: self.tcx,
            typing_env: self.analysis_key().typing_env(self.tcx),
            body: &self.body,
            locals: DenseBitSet::new_empty(self.body.local_decls.len()),
        };
        let loc = mir::Location::START;
        use mir::visit::Visitor as _;
        if statement_index < data.statements.len() {
            visitor.visit_statement(&data.statements[statement_index], loc);
        } else if let Some(tmnt) = &data.terminator {
            visitor.visit_terminator(tmnt, loc);
        }
        visitor.locals
    }

    // XXX: In nightly-2024-09-08, `MaybeInitializedPlaces::switch_int_edge_effects`
    //      requires `SwitchInt` values to be in the same order as `AdtDef::discriminants`.
    //      Since optimizations can sometimes break this order, we normalize it beforehand.
    //
    // > thread 'rustc' panicked at /rustc/12b26c13fba25c9e1bc2fdf05f3c2dbb851c83de/compiler/rustc_mir_dataflow/src/impls/initialized.rs:431:18:
    // > Order of `AdtDef::discriminants` differed from `SwitchInt::values`
    fn normalize_switch_int_discriminant_order(&mut self) {
        let blocks = self.body.basic_blocks.as_mut().as_mut_slice();
        for block in blocks.iter_mut() {
            let Some(terminator) = &mut block.terminator else {
                continue;
            };
            let mir::TerminatorKind::SwitchInt { discr, targets } = &mut terminator.kind else {
                continue;
            };
            let Some(discr_place) = discr.place() else {
                continue;
            };

            let enum_adt = block.statements.iter().rev().find_map(|stmt| {
                let mir::StatementKind::Assign(assign) = &stmt.kind else {
                    return None;
                };
                let (lhs, mir::Rvalue::Discriminant(disc_place)) = assign.as_ref() else {
                    return None;
                };
                if *lhs != discr_place {
                    return None;
                }
                let ty = disc_place.ty(&self.body.local_decls, self.tcx).ty;
                if let mir_ty::TyKind::Adt(def, _) = ty.kind() {
                    Some(*def)
                } else {
                    None
                }
            });
            let Some(adt_def) = enum_adt else {
                continue;
            };

            let otherwise = targets.otherwise();
            let mut pairs: Vec<(u128, mir::BasicBlock)> = targets.iter().collect();
            let discriminant_order: Vec<u128> = adt_def
                .discriminants(self.tcx)
                .map(|(_, discr)| discr.val)
                .collect();
            pairs.sort_by_key(|(val, _)| {
                discriminant_order
                    .iter()
                    .position(|d| d == val)
                    .unwrap_or(usize::MAX)
            });
            *targets = mir::SwitchTargets::new(pairs.into_iter(), otherwise);
        }
    }

    /// The move paths of the body, gathered on a copy whose `CopyForDeref` destinations are
    /// marked as deref temporaries.
    fn move_data(&self) -> MoveData<'tcx> {
        let mut body = self.body.clone();
        struct Visitor {
            deref_temps: DenseBitSet<Local>,
        }
        impl<'tcx> mir::visit::Visitor<'tcx> for Visitor {
            fn visit_assign(
                &mut self,
                place: &mir::Place<'tcx>,
                rvalue: &mir::Rvalue<'tcx>,
                _location: mir::Location,
            ) {
                if let mir::Rvalue::CopyForDeref { .. } = rvalue {
                    self.deref_temps.insert(place.local);
                }
            }
        }
        let mut visitor = Visitor {
            deref_temps: DenseBitSet::new_empty(body.local_decls.len()),
        };
        use mir::visit::Visitor as _;
        visitor.visit_body(&body);
        for (local, local_decl) in body.local_decls.iter_enumerated_mut() {
            let local_info = if visitor.deref_temps.contains(local) {
                mir::LocalInfo::DerefTemp
            } else {
                mir::LocalInfo::Boring
            };
            local_decl.local_info = mir::ClearCrossCrate::Set(Box::new(local_info));
        }
        MoveData::gather_moves(&body, self.tcx, |_| true)
    }

    fn zst_locals(&self) -> DenseBitSet<Local> {
        let typing_env = self.analysis_key().typing_env(self.tcx);
        let mut zst_locals = DenseBitSet::new_empty(self.body.local_decls.len());
        for (local, local_decl) in self.body.local_decls.iter_enumerated() {
            if self
                .tcx
                .layout_of(typing_env.as_query_input(local_decl.ty))
                .map(|l| l.is_zst())
                .unwrap_or(false)
            {
                zst_locals.insert(local);
            }
        }
        zst_locals
    }

    fn reassign_local_mutabilities(&mut self, move_data: &MoveData<'tcx>) {
        for local_decl in &mut self.body.local_decls {
            local_decl.mutability = mir::Mutability::Not;
        }

        let zst_locals = self.zst_locals();
        let mut marked = Vec::new();
        let mut results = MaybeInitializedPlaces::new(self.tcx, &self.body, move_data)
            .iterate_to_fixpoint(self.tcx, &self.body, None)
            .into_results_cursor(&self.body);
        for (block, data) in mir::traversal::preorder(&self.body) {
            for statement_index in 0..=data.statements.len() {
                let loc = mir::Location {
                    statement_index,
                    block,
                };
                results.seek_before_primary_effect(loc);
                let MaybeReachable::Reachable(init_places) = results.get() else {
                    continue;
                };
                let init_locals = locals_of(init_places.iter(), move_data);
                let mut_locals = self.mut_locals(data, statement_index);
                tracing::info!(
                    ?init_locals,
                    ?mut_locals,
                    ?zst_locals,
                    ?statement_index,
                    ?block,
                    stmt = ?data.statements.get(statement_index),
                );
                for mut_local in mut_locals.iter() {
                    if init_locals.contains(&mut_local) || zst_locals.contains(mut_local) {
                        marked.push(mut_local);
                        tracing::info!(?mut_local, ?statement_index, ?block, "marking mut");
                    }
                }
            }
        }
        for local in marked {
            self.body.local_decls[local].mutability = mir::Mutability::Mut;
        }
    }

    /// Scans the body for loop-invariant marker calls and groups them by
    /// enclosing loop header. Multiple invariants for the same header are kept
    /// in source order; the caller is responsible for AND'ing them. Each carries
    /// the marker it was written with.
    fn collect_loop_invariant_annotations(
        &self,
    ) -> HashMap<BasicBlock, Vec<(LocalDefId, mir_ty::GenericArgsRef<'tcx>, InvariantMarker)>> {
        let mut loop_invariants: HashMap<_, Vec<_>> = HashMap::new();
        for (bb, data) in self.body.basic_blocks.iter_enumerated() {
            let Some(term) = &data.terminator else {
                continue;
            };
            let mir::TerminatorKind::Call { func, args, .. } = &term.kind else {
                continue;
            };
            let Some((def_id, _)) = func.const_fn_def() else {
                continue;
            };
            let Some(marker) = self.ctx.def_ids().invariant_marker_kind(def_id) else {
                continue;
            };

            let arg_ty = args[0].node.ty(&self.body.local_decls, self.tcx);
            let mir_ty::TyKind::FnDef(formula_def_id, generic_args) = arg_ty.kind() else {
                panic!("invariant marker argument must be a formula function item");
            };
            let formula_def_id = formula_def_id
                .as_local()
                .expect("invariant formula function must be local");
            let header = Self::loop_header_of(&self.body, bb).unwrap_or_else(|| {
                panic!("no enclosing loop header for invariant marker at {bb:?}")
            });
            loop_invariants.entry(header).or_default().push((
                formula_def_id,
                *generic_args,
                marker,
            ));
        }
        loop_invariants
    }

    /// Walks up the dominator tree from the marker block to the innermost
    /// enclosing loop header: the first dominator that needs its own
    /// precondition (in-degree >= 2) and has a back edge.
    fn loop_header_of(body: &Body<'_>, marker_bb: BasicBlock) -> Option<BasicBlock> {
        let doms = body.basic_blocks.dominators();
        let preds = body.basic_blocks.predecessors();
        let mut cur = Some(marker_bb);
        while let Some(bb) = cur {
            if analyze::basic_block::needs_own_precondition(body, bb)
                && preds[bb].iter().any(|&p| doms.dominates(bb, p))
            {
                return Some(bb);
            }
            cur = doms.immediate_dominator(bb);
        }
        None
    }

    /// Resolves the live local matching a source variable name at the given
    /// basic block, among the locals that are parameters of `bty`.
    ///
    /// When several distinct live locals share the name (e.g. two shadowed
    /// variables that are both loop-carried), the mapping is ambiguous; rather
    /// than silently pick one, this raises a fatal error. Disambiguating which
    /// shadow an invariant refers to is left as future work.
    fn local_of_name_in_bb(&self, name: rustc_span::Symbol, bty: &BasicBlockType) -> Option<Local> {
        let mut found: Option<Local> = None;
        for vdi in &self.body.var_debug_info {
            tracing::debug!("comparing {name:?} with {vdi:?}...");
            if vdi.name != name {
                tracing::debug!("different name, skip.");
                continue;
            }
            let mir::VarDebugInfoContents::Place(place) = vdi.value else {
                tracing::debug!("place, skip.");
                continue;
            };
            if !place.projection.is_empty() {
                tracing::debug!("empty projection, skip.");
                continue;
            }
            if bty.param_of_local(place.local).is_none() {
                tracing::debug!("not param of local, skip.");
                continue;
            }
            tracing::debug!("found.");
            match found {
                None => found = Some(place.local),
                Some(prev) if prev == place.local => {}
                Some(_) => self.tcx.dcx().fatal(format!(
                    "loop invariant refers to `{name}`, which is ambiguous at the loop header: \
                     multiple live variables share this name (e.g. through shadowing). \
                     Rename the variables to disambiguate."
                )),
            }
        }
        found
    }

    fn function_param_local_of_name(&self, name: rustc_span::Symbol) -> Option<Local> {
        let mut found: Option<Local> = None;
        for vdi in &self.body.var_debug_info {
            tracing::debug!("comparing {name:?} with {vdi:?}...");
            if vdi.name != name {
                tracing::debug!("different name, skip.");
                continue;
            }
            let mir::VarDebugInfoContents::Place(place) = vdi.value else {
                tracing::debug!("place, skip.");
                continue;
            };
            if !place.projection.is_empty() {
                tracing::debug!("empty projection, skip.");
                continue;
            }
            let local = place.local;
            if local.index() == 0 || local.index() > self.body.arg_count {
                tracing::debug!("not param of local, skip.");
                continue;
            }
            tracing::debug!("found.");
            match found {
                None => found = Some(local),
                Some(prev) if prev == local => {}
                Some(_) => panic!("multiple function arguments share the name `{name}`"),
            }
        }
        found
    }

    fn expand_model_projection(&self, ty: mir_ty::Ty<'tcx>) -> mir_ty::Ty<'tcx> {
        if let mir_ty::Alias(mir_ty::AliasTyKind::Projection, ty) = ty.kind() {
            if let Some(model_ty_def_id) = self.ctx.def_ids.model_ty() {
                let arg_ty = ty.args.type_at(0);

                if ty.def_id == model_ty_def_id {
                    return arg_ty;
                }
            }
        }
        ty
    }

    /// Translates a user-provided loop invariant (a formula function over named
    /// live variables) into a precondition refinement over `bty`'s parameters.
    /// Each formula parameter names a live variable at the loop header and is
    /// mapped to the corresponding basic-block parameter.
    ///
    /// A parameter typed `FnParam<..>` instead names the enclosing function's
    /// parameter of that name, and stands for its value on entry rather than the
    /// loop-carried one. The receiver participates under the name `self`, the name
    /// its debug info carries; the lifted formula function spells it
    /// `__thrust_self`, which [`analyze::annot_fn::lifted_param_source_name`] maps
    /// back before the lookup.
    fn build_invariant_precondition(
        &self,
        formula_def_id: LocalDefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        bty: &BasicBlockType,
    ) -> rty::Refinement<rty::FunctionParamIdx> {
        let formula_fn = self
            .ctx
            .formula_fn_with_args(formula_def_id, generic_args, self.owner_fn_id)
            .expect("invariant formula function is not registered");
        let idents = formula_fn.param_idents();
        let sig = self
            .tcx
            .fn_sig(formula_def_id.to_def_id())
            .instantiate(self.tcx, generic_args);

        let mut mapping: Vec<rty::FunctionParamIdx> = Vec::with_capacity(idents.len());
        for (ident, input_ty) in idents.iter().zip(sig.skip_binder().inputs()) {
            let ident = ident.expect("invariant parameters must be named");
            let input_ty = {
                let typing_env =
                    mir_ty::TypingEnv::post_analysis(self.tcx, formula_def_id.to_def_id());
                self.tcx
                    .try_normalize_erasing_regions(typing_env, *input_ty)
                    .unwrap_or(*input_ty)
            };

            let input_ty = self.expand_model_projection(input_ty);
            tracing::debug!(?ident, ?input_ty, "resolving");

            let name = analyze::annot_fn::lifted_param_source_name(ident);

            if input_ty
                .ty_adt_def()
                .is_some_and(|def| Some(def.did()) == self.ctx.def_ids().fn_param_wrapper())
            {
                tracing::debug!("fn_param_local: {input_ty:?}");
                let local = self.function_param_local_of_name(name).unwrap_or_else(|| {
                    self.tcx.dcx().fatal(format!(
                        "loop invariant refers to `{name}` via FnParam, but it is not a function parameter"
                    ))
                });
                let param_idx = crate::analyze::function_param_of_local(local);
                mapping.push(bty.param_of_outer_fn_param(param_idx).unwrap());
            } else {
                tracing::debug!("local: {input_ty:?}");
                let local = self.local_of_name_in_bb(name, bty).unwrap_or_else(|| {
                    self.tcx.dcx().fatal(format!(
                        "loop invariant refers to `{name}`, which is not a live variable at the loop header"
                    ))
                });
                mapping.push(bty.param_of_local(local).unwrap());
            }
        }

        formula_fn
            .formula()
            .clone()
            .subst_var(|idx| chc::Term::var(rty::RefinedTypeVar::Free(mapping[idx.index()])))
            .into()
    }

    fn refine_basic_blocks(&mut self, move_data: &MoveData<'tcx>) {
        let loop_invariants = self.collect_loop_invariant_annotations();
        for (header, invariants) in &loop_invariants {
            let formulas = invariants.iter().map(|(formula, _, _)| *formula);
            self.ctx
                .record_invariant_annotations(self.local_def_id, *header, formulas);
        }
        let zst_locals = self.zst_locals();
        let mut results = MaybeLiveLocals
            .iterate_to_fixpoint(self.tcx, &self.body, None)
            .into_results_cursor(&self.body);
        let mut ever_init = EverInitializedPlaces::new(&self.body, move_data)
            .iterate_to_fixpoint(self.tcx, &self.body, None)
            .into_results_cursor(&self.body);
        let mut uninit = MaybeUninitializedPlaces::new(self.tcx, &self.body, move_data)
            .iterate_to_fixpoint(self.tcx, &self.body, None)
            .into_results_cursor(&self.body);
        let mut moves = analyze::basic_block::MoveState {
            tcx: self.tcx,
            typing_env: self.analysis_key().typing_env(self.tcx),
            move_data,
            uninit: &mut uninit,
        };

        let mut builder = analyze::basic_block::DropPoints::builder(&self.body);
        for (bb, _data) in mir::traversal::postorder(&self.body) {
            let span = tracing::info_span!("refine_basic_block", ?bb, bb_index = bb.as_u32());
            let _guard = span.enter();

            self.drop_points
                .insert(bb, builder.build(&mut results, &mut moves, bb));
            results.seek_to_block_start(bb);
            // A local never set on any path here is live only for a drop that its drop flag
            // skips, and holds no value, so it is no parameter of the block; an edge into a block
            // where it may be set passes it as any value. A ZST's one value needs no setting.
            ever_init.seek_to_block_start(bb);
            let ever_set = locals_of(
                ever_init
                    .get()
                    .iter()
                    .map(|init| move_data.inits[init].path),
                move_data,
            );
            let mut live_locals: Vec<_> = results
                .get()
                .iter()
                .filter(|local| zst_locals.contains(*local) || ever_set.contains(local))
                .map(|in_local| {
                    let decl = &self.body.local_decls[in_local];
                    let type_and_mut = TypeAndMut {
                        ty: decl.ty,
                        mutbl: decl.mutability,
                    };
                    (in_local, type_and_mut)
                })
                .collect();
            // TODO: ad-hoc
            if bb == mir::START_BLOCK {
                for a in self.body.args_iter() {
                    if live_locals.iter().any(|(l, _)| *l == a) {
                        continue;
                    }
                    let decl = &self.body.local_decls[a];
                    let type_and_mut = TypeAndMut {
                        ty: decl.ty,
                        mutbl: decl.mutability,
                    };
                    live_locals.push((a, type_and_mut));
                    self.drop_points
                        .get_mut(&bb)
                        .unwrap()
                        .before_statements
                        .push(a);
                }
            }
            let previous = self
                .ctx
                .enter_template_site(analyze::TemplateSite::Block(self.local_def_id, bb));
            // function return type is basic block return type
            let ret_ty = self.body.local_decls[mir::RETURN_PLACE].ty;
            if let Some(invariants) = loop_invariants.get(&bb) {
                // A user-supplied loop invariant fully replaces inference: build
                // the block type without a precondition pvar and install the
                // invariant as its precondition. Multiple `invariant!` calls at
                // the same header are AND'd in source order.
                //
                // When one of them is partial (`partial_invariant!`), the block
                // instead keeps the template's predicate variable and the
                // invariants are conjoined to it, so inference fills in what the
                // annotations leave out.
                let partial = invariants
                    .iter()
                    .any(|&(_, _, marker)| marker == InvariantMarker::Partial);
                let mut bty = if partial {
                    self.type_builder
                        .for_template(&mut self.ctx)
                        .build_basic_block(&self.body, live_locals, ret_ty)
                } else {
                    self.type_builder
                        .build_basic_block(&self.body, live_locals, ret_ty)
                };
                let mut inv = rty::Refinement::top();
                for &(formula_def_id, generic_args, _) in invariants {
                    let one = self.build_invariant_precondition(formula_def_id, generic_args, &bty);
                    inv.push_conj(one);
                }
                // For a full invariant the block's precondition holds only what the types of its
                // parameters say (see `FunctionTemplateTypeBuilder::build`), so conjoining
                // keeps that and adds the invariant.
                bty.conjoin_precondition(inv);
                self.ctx
                    .register_basic_block_ty_with_precondition(self.analysis_key(), bb, bty);
            } else if analyze::basic_block::needs_own_precondition(&self.body, bb) {
                let bty = self
                    .type_builder
                    .for_template(&mut self.ctx)
                    .build_basic_block(&self.body, live_locals, ret_ty);
                self.ctx
                    .register_basic_block_ty_with_precondition(self.analysis_key(), bb, bty);
            } else {
                // The block inherits its predecessor's outgoing env state as its
                // precondition, materialized lazily during the predecessor's
                // analysis. Record only unrefined type here.
                let bty = self
                    .type_builder
                    .build_basic_block(&self.body, live_locals, ret_ty);
                self.ctx
                    .register_basic_block_ty_without_precondition(self.analysis_key(), bb, bty);
            };
            self.ctx.leave_template_site(previous);
        }
    }

    fn analyze_basic_blocks(&mut self, expected_fn_ty: &rty::RefinedType) {
        let expected_fn_ty = expected_fn_ty.ty.as_function().unwrap();
        let mut entry = self
            .ctx
            .basic_block_ty(self.analysis_key(), mir::START_BLOCK)
            .clone();
        let mut expected_entry = expected_fn_ty.clone();
        self.elaborate_mut_params(&mut expected_entry);
        for idx in entry.as_ref().params.indices().collect::<Vec<_>>() {
            let argument = match entry.param_kind(idx) {
                crate::refine::BasicBlockTypeParamKind::Local(local, _) => self
                    .body
                    .args_iter()
                    .position(|arg| arg == local)
                    .map(rty::FunctionParamIdx::from),
                crate::refine::BasicBlockTypeParamKind::OuterFnParam(argument) => Some(argument),
                crate::refine::BasicBlockTypeParamKind::Synthetic => None,
                crate::refine::BasicBlockTypeParamKind::Captured => unreachable!(),
            };
            if let Some(argument) = argument {
                let ty = expected_entry.params[argument].ty.clone().map_var(|arg| {
                    entry
                        .param_of_local(analyze::local_of_function_param(arg))
                        .unwrap()
                });
                entry.set_param_type(idx, ty);
            }
        }
        self.ctx.register_basic_block_ty_with_precondition(
            self.analysis_key(),
            mir::START_BLOCK,
            entry,
        );
        // Reverse postorder guarantees each block that inherits its precondition
        // is visited after the predecessor that lazily materialized its type.
        for (bb, data) in mir::traversal::reverse_postorder(&self.body) {
            if data.is_cleanup {
                continue;
            }
            let rty = self
                .ctx
                .basic_block_ty_with_precondition(self.analysis_key(), bb)
                .clone();
            let drop_points = self.drop_points[&bb].clone();
            self.ctx
                .basic_block_analyzer(self.analysis_key(), bb)
                .body(self.body.clone())
                .drop_points(drop_points)
                .run(&rty, expected_fn_ty);
        }
    }

    fn elaborate_mut_params(&self, fn_ty: &mut rty::FunctionType) {
        if self.body.arg_count == 0 {
            return;
        }

        for (param_idx, param_ty) in fn_ty.params.iter_enumerated_mut() {
            let ty = if self.is_mut_param(param_idx) {
                rty::PointerType::own(param_ty.ty.clone()).into()
            } else {
                param_ty.ty.clone()
            };
            *param_ty = rty::RefinedType::new(
                ty,
                param_ty
                    .refinement
                    .clone()
                    .subst_value_var(|| {
                        if self.is_mut_param(param_idx) {
                            chc::Term::var(rty::RefinedTypeVar::Value).box_current()
                        } else {
                            chc::Term::var(rty::RefinedTypeVar::Value)
                        }
                    })
                    .subst_free_var(|v| {
                        if self.is_mut_param(v) {
                            chc::Term::var(v).box_current()
                        } else {
                            chc::Term::var(v)
                        }
                    }),
            );
        }

        fn_ty.ret.refinement = fn_ty.ret.refinement.clone().subst_free_var(|v| {
            if self.is_mut_param(v) {
                chc::Term::var(v).box_current()
            } else {
                chc::Term::var(v)
            }
        });
    }

    /// Drop excessive parameters from the BB-side entry function type that do not
    /// correspond to any function argument. These are introduced by ZST locals whose
    /// liveness analysis treats them as live without an explicit def.
    fn drop_bb_zst_params(&self, bb_ty: &BasicBlockType) -> rty::FunctionType {
        let mut fn_ty = bb_ty.to_function_ty();
        let arg_locals: HashSet<_> = self.body.args_iter().collect();

        for idx in bb_ty.local_params().rev() {
            let local = bb_ty.local_of_param(idx).unwrap();
            if !arg_locals.contains(&local) {
                fn_ty.remove_param(idx);
            }
        }

        // A function type must keep at least one parameter to host the precondition
        // predicate. When the function has no real argument, both the expected type and
        // the BB type carry a synthetic unit parameter (see
        // `crate::refine::TypeBuilder::build_basic_block`). That synthetic has no
        // backing local, so it survives the drop loop untouched. If instead the entry
        // block exposed only ZST-local parameters (e.g. `RETURN_PLACE`), dropping them
        // empties the type, and we re-introduce the synthetic unit parameter carrying
        // the precondition refinement of the last dropped parameter.
        if self.body.arg_count == 0 && fn_ty.params.is_empty() {
            let refinement = bb_ty.as_ref().last_param().unwrap().refinement.clone();
            fn_ty
                .params
                .push(rty::RefinedType::new(rty::Type::unit(), refinement));
        }

        fn_ty
    }

    /// Drop function parameters from `expected_ty` whose corresponding local is unused
    /// (and thus not represented) in the BB-side entry function type.
    fn drop_unused_expected_params(
        &self,
        expected_ty: &mut rty::FunctionType,
        bb_ty: &BasicBlockType,
    ) {
        if self.body.arg_count == 0 {
            return;
        }
        let arg_locals: HashSet<_> = self.body.args_iter().collect();
        let present_arg_locals: HashSet<_> = bb_ty
            .locals()
            .filter(|local| arg_locals.contains(local))
            .collect();
        for idx in expected_ty.params.indices().rev() {
            let arg_local = analyze::local_of_function_param(idx);
            if !present_arg_locals.contains(&arg_local) {
                expected_ty.remove_param(idx);
            }
        }
    }

    fn assert_entry(&mut self, expected: &rty::RefinedType) {
        let mut entry_ty = self
            .ctx
            .basic_block_ty_with_precondition(self.analysis_key(), mir::START_BLOCK)
            .clone();
        tracing::debug!(expected = %expected.display(), entry = %entry_ty.display(), "assert_entry before");
        let mut expected = expected.ty.as_function().cloned().unwrap();
        self.elaborate_mut_params(&mut expected);

        entry_ty.truncate_outer_fn_params();
        self.drop_unused_expected_params(&mut expected, &entry_ty);
        let entry_ty = self.drop_bb_zst_params(&entry_ty);

        tracing::debug!(expected = %expected.display(), entry = %entry_ty.display(), "assert_entry after");
        let clauses = rty::relate_sub_param_types(&entry_ty.params, &expected.params);
        self.ctx.extend_clauses(clauses);
    }
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    pub fn new(ctx: &'ctx mut analyze::Analyzer<'tcx>, local_def_id: LocalDefId) -> Self {
        let tcx = ctx.tcx;
        let body = tcx.optimized_mir(local_def_id.to_def_id()).clone();
        let drop_points = Default::default();
        let (owner_fn_id, owner_fn_id_args) =
            if is_annotated_as_extern_spec_fn_impl(&tcx, &local_def_id) {
                let (def_id, args) = extern_spec_fn_target_def_id_impl(&tcx, &local_def_id, &body);
                (def_id, Some(args))
            } else {
                (local_def_id.to_def_id(), None)
            };
        let type_builder = ctx.type_builder(ctx.def_ids(), owner_fn_id);
        let generic_args = mir_ty::GenericArgs::identity_for_item(tcx, local_def_id);
        Self {
            ctx,
            tcx,
            local_def_id,
            owner_fn_id,
            owner_fn_id_args,
            body,
            generic_args,
            drop_points,
            type_builder,
        }
    }

    pub fn local_def_id(&self) -> LocalDefId {
        self.local_def_id
    }

    pub fn analysis_key(&self) -> analyze::AnalysisKey<'tcx> {
        analyze::AnalysisKey::new(self.local_def_id, self.generic_args, self.owner_fn_id)
    }

    pub fn owner_fn_id(&mut self, owner_fn_id: DefId) -> &mut Self {
        tracing::debug!(
            "change owner_fn_id from {:?} to {:?}.",
            self.owner_fn_id,
            owner_fn_id
        );
        self.owner_fn_id = owner_fn_id;
        self.type_builder = self.ctx.type_builder(self.ctx.def_ids(), owner_fn_id);
        self
    }

    pub fn generic_args(&mut self, generic_args: mir_ty::GenericArgsRef<'tcx>) -> &mut Self {
        use mir_ty::TypeVisitableExt as _;

        self.generic_args = generic_args;
        let body = mir_ty::EarlyBinder::bind(self.body.clone());
        // Substitution on its own leaves `<I as Iterator>::Item` behind as
        // `<Range as Iterator>::Item`. Resolving that projection has to happen here, while
        // the arguments still carry the real closure type: once the type builder has
        // swapped a closure for its model the impl no longer applies, the projection can
        // never be resolved, and it degrades into a fresh abstract sort that the rest of
        // the signature disagrees with.
        //
        // Arguments that still mention type parameters describe the generic template,
        // where there is nothing to resolve and a monomorphized environment would not
        // apply, so those keep the plain substitution.
        let resolved = if generic_args.has_param() {
            None
        } else {
            self.tcx
                .try_instantiate_and_normalize_erasing_regions(
                    generic_args,
                    mir_ty::TypingEnv::fully_monomorphized(),
                    body.clone(),
                )
                .ok()
        };
        self.body = resolved.unwrap_or_else(|| body.instantiate(self.tcx, generic_args));
        self
    }

    /// The blocks of the natural loops whose head is `bb`, or `None` if `bb` heads no loop.
    fn natural_loop(&self, bb: BasicBlock) -> Option<HashSet<BasicBlock>> {
        let dominators = self.body.basic_blocks.dominators();
        let preds = &self.body.basic_blocks.predecessors();
        let mut pending: Vec<_> = preds[bb]
            .iter()
            .copied()
            .filter(|&p| dominators.dominates(bb, p))
            .collect();
        if pending.is_empty() {
            return None;
        }
        let mut blocks = HashSet::from([bb]);
        while let Some(b) = pending.pop() {
            if blocks.insert(b) {
                pending.extend(preds[b].iter().copied());
            }
        }
        Some(blocks)
    }

    /// The predicate variable of the precondition of `bb`, when it is left to inference.
    fn precondition_pred_var(&self, bb: BasicBlock) -> Option<chc::PredVarId> {
        let bty = self
            .ctx
            .basic_block_ty_with_precondition(self.analysis_key(), bb);
        let fn_ty = bty.to_function_ty();
        let precondition = &fn_ty.params.raw.last()?.refinement;
        precondition
            .body
            .atoms
            .iter()
            .find_map(|atom| match atom.pred {
                chc::Pred::Var(p) => Some(p),
                _ => None,
            })
    }

    /// The facts of the precondition of `bb` besides its predicate variable (`x >= 0` of an
    /// unsigned parameter), over that variable's arguments by position.
    fn precondition_facts(&self, bb: BasicBlock) -> Vec<chc::Formula> {
        let bty = self
            .ctx
            .basic_block_ty_with_precondition(self.analysis_key(), bb);
        let fn_ty = bty.to_function_ty();
        let Some(param) = fn_ty.params.raw.last() else {
            return Vec::new();
        };
        let body = &param.refinement.body;
        let Some(pred_atom) = body
            .atoms
            .iter()
            .find(|atom| matches!(atom.pred, chc::Pred::Var(_)))
        else {
            return Vec::new();
        };
        let mut position = HashMap::new();
        for (k, arg) in pred_atom.args.iter().enumerate() {
            let at = chc::Term::var(chc::TermVarIdx::from_usize(k));
            match arg {
                chc::Term::Var(v) => position.insert(*v, at),
                chc::Term::BoxCurrent(t) => match &**t {
                    chc::Term::Var(v) => position.insert(*v, chc::Term::box_(at)),
                    _ => None,
                },
                _ => None,
            };
        }
        body.atoms
            .iter()
            .filter(|atom| !matches!(atom.pred, chc::Pred::Var(_)))
            .cloned()
            .map(chc::Formula::Atom)
            .chain(chc::conjuncts(&body.formula))
            .filter(|fact| fact.fv().all(|v| position.contains_key(v)))
            .map(|fact| fact.subst_var(|v| position[&v].clone()))
            .collect()
    }

    /// Declares candidate atoms for the predicate variable of each loop head: the conjuncts of
    /// this function's contract and of the contracts of the functions its loop calls, each
    /// instantiated at the terms over the head's arguments of the matching sorts, and the
    /// prophecy equalities of the references the head carries.
    fn declare_candidate_atoms(&mut self, expected: &rty::RefinedType) {
        let fn_ty = expected.ty.as_function().unwrap().clone();
        for bb in self.body.basic_blocks.indices() {
            if bb == mir::START_BLOCK
                || self.body.basic_blocks[bb].is_cleanup
                || !analyze::basic_block::needs_own_precondition(&self.body, bb)
            {
                continue;
            }
            let Some(loop_blocks) = self.natural_loop(bb) else {
                continue;
            };
            let Some(pred) = self.precondition_pred_var(bb) else {
                continue;
            };
            let sig = self.ctx.pred_var_sig(pred);
            tracing::debug!(?bb, ?pred, ?sig, "candidate atoms for loop head");
            let head = chc::HeadTerms::new(&sig);
            let mut atoms = head.prophecy_atoms();
            if chc::CandidateAtomsMode::from_env() == chc::CandidateAtomsMode::ContractsAndEntry {
                atoms.extend(self.precondition_facts(bb));
            }
            atoms.extend(contract_instances(&fn_ty, &head, ContractSource::Enclosing));
            let mut loop_blocks: Vec<_> = loop_blocks.into_iter().collect();
            loop_blocks.sort();
            for b in loop_blocks {
                for callee in self.ctx.called_fn_tys(self.analysis_key(), b) {
                    tracing::debug!(?b, callee = %callee.display(), "candidate atoms from callee");
                    atoms.extend(contract_instances(callee, &head, ContractSource::Callee));
                }
            }
            atoms.truncate(MAX_CANDIDATE_ATOMS);
            self.ctx.push_candidate_atoms(pred, atoms);
        }
    }

    pub fn run(&mut self, expected: &rty::RefinedType) {
        let span = tracing::info_span!(
            "def",
            def = %self.tcx.def_path_str(self.local_def_id),
            def_index = self.local_def_id.local_def_index.as_u32()
        );
        let _guard = span.enter();

        self.ctx
            .body_checks()
            .record(self.local_def_id, analyze::BodyCheck::Checked);
        self.unelaborate_derefs();
        analyze::reconstruct_slice_indexing::reconstruct(self.tcx, &mut self.body);
        analyze::two_phase_borrow::move_to_activation(self.tcx, &mut self.body);
        self.normalize_switch_int_discriminant_order();
        let move_data = self.move_data();
        self.reassign_local_mutabilities(&move_data);
        self.refine_basic_blocks(&move_data);
        self.analyze_basic_blocks(expected);
        self.assert_entry(expected);
        if analyze::candidate_atoms_enabled() {
            self.declare_candidate_atoms(expected);
        }
    }
}

/// A deref temporary that is not replaced: a copy of its place, which is reborrowed where it
/// is a `&mut` (`ReborrowVisitor`), as the reborrow it stands for.
fn kept_deref_temp<'tcx>(
    stmt: &mir::Statement<'tcx>,
    temp: Local,
    place: mir::Place<'tcx>,
) -> mir::StatementKind<'tcx> {
    let mir::StatementKind::Assign(assign) = &stmt.kind else {
        unreachable!()
    };
    if !matches!(assign.1, mir::Rvalue::CopyForDeref(_)) {
        unimplemented!("Box pointer {temp:?} of {place:?} used after the Box may have changed");
    }
    let rvalue = mir::Rvalue::Use(mir::Operand::Copy(place));
    mir::StatementKind::Assign(Box::new((temp.into(), rvalue)))
}

/// `uses` with the uses of each temporary of `replaced` added to those of the temporaries its
/// place goes through, transitively.
fn with_uses_through_copies<'tcx>(
    mut uses: HashMap<Local, Vec<mir::Location>>,
    replaced: &[(Local, mir::Location, mir::Place<'tcx>)],
) -> HashMap<Local, Vec<mir::Location>> {
    let mut changed = true;
    while changed {
        changed = false;
        for (child, child_def, _) in replaced {
            let child_uses = uses.get(child).cloned().unwrap_or_default();
            for (parent, _, _) in replaced {
                let parent_uses = uses.entry(*parent).or_default();
                if !parent_uses.contains(child_def) {
                    continue;
                }
                for loc in &child_uses {
                    if !parent_uses.contains(loc) {
                        parent_uses.push(*loc);
                        changed = true;
                    }
                }
            }
        }
    }
    uses
}

fn location_successors(body: &Body<'_>, loc: mir::Location) -> Vec<mir::Location> {
    let data = &body.basic_blocks[loc.block];
    if loc.statement_index < data.statements.len() {
        return vec![loc.successor_within_block()];
    }
    data.terminator()
        .successors()
        .map(|bb| bb.start_location())
        .collect()
}

/// The locations of the statements and terminators that mention each local.
fn local_mentions(body: &Body<'_>) -> HashMap<Local, Vec<mir::Location>> {
    struct Visitor {
        mentions: HashMap<Local, Vec<mir::Location>>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Visitor {
        fn visit_local(
            &mut self,
            local: Local,
            context: mir::visit::PlaceContext,
            location: mir::Location,
        ) {
            if !matches!(context, mir::visit::PlaceContext::NonUse(_)) {
                self.mentions.entry(local).or_default().push(location);
            }
        }
    }
    let mut visitor = Visitor {
        mentions: HashMap::new(),
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        mir::visit::Visitor::visit_basic_block_data(&mut visitor, block, data);
    }
    visitor.mentions
}

/// At most this many instances of one contract conjunct, and candidate atoms of one loop head.
const MAX_INSTANCES_PER_CONJUNCT: usize = 256;
const MAX_CANDIDATE_ATOMS: usize = 512;

/// Whose contract a loop head's candidate atoms are read from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ContractSource {
    /// The function the loop is in: its requires and ensures.
    Enclosing,
    /// A function the loop calls. Its arguments and result are values of one iteration, so
    /// only the conjuncts over its reference parameters are kept: what `*r` and `^r` of a
    /// reference into the loop's state satisfy (an iterator's `invariant(*self)`).
    Callee,
}

/// The instances at `head` of the conjuncts of `fn_ty`'s contract.
fn contract_instances(
    fn_ty: &rty::FunctionType,
    head: &chc::HeadTerms,
    source: ContractSource,
) -> Vec<chc::Formula> {
    let param_sorts: Vec<chc::Sort> = fn_ty.params.iter().map(|p| p.ty.to_sort()).collect();
    let is_reference = |sort: &chc::Sort| matches!(sort, chc::Sort::Mut(_) | chc::Sort::Box(_));
    let mut out = Vec::new();
    for (idx, param) in fn_ty.params.iter_enumerated() {
        let value_sort = param_sorts[idx.index()].clone();
        let keep = |v: &rty::RefinedTypeVar<rty::FunctionParamIdx>| match (source, v) {
            (ContractSource::Enclosing, _) => true,
            (ContractSource::Callee, rty::RefinedTypeVar::Value) => is_reference(&value_sort),
            (ContractSource::Callee, rty::RefinedTypeVar::Free(j)) => {
                is_reference(&param_sorts[j.index()])
            }
            (ContractSource::Callee, rty::RefinedTypeVar::Existential(_)) => true,
        };
        out.extend(refinement_instances(
            &param.refinement,
            &value_sort,
            &param_sorts,
            head,
            &keep,
        ));
    }
    let keep = |v: &rty::RefinedTypeVar<rty::FunctionParamIdx>| match (source, v) {
        (ContractSource::Enclosing, _) => true,
        (ContractSource::Callee, rty::RefinedTypeVar::Value) => false,
        (ContractSource::Callee, rty::RefinedTypeVar::Free(j)) => {
            is_reference(&param_sorts[j.index()])
        }
        (ContractSource::Callee, rty::RefinedTypeVar::Existential(_)) => true,
    };
    out.extend(refinement_instances(
        &fn_ty.ret.refinement,
        &fn_ty.ret.ty.to_sort(),
        &param_sorts,
        head,
        &keep,
    ));
    out
}

/// The instances at `head` of the conjuncts of `refinement` whose variables all pass `keep`.
/// `value_sort` is the sort of the refined value, `param_sorts` those of the function's
/// parameters.
fn refinement_instances(
    refinement: &rty::Refinement<rty::FunctionParamIdx>,
    value_sort: &chc::Sort,
    param_sorts: &[chc::Sort],
    head: &chc::HeadTerms,
    keep: &dyn Fn(&rty::RefinedTypeVar<rty::FunctionParamIdx>) -> bool,
) -> Vec<chc::Formula> {
    let var_sort = |v: &rty::RefinedTypeVar<rty::FunctionParamIdx>| match v {
        rty::RefinedTypeVar::Value => Some(value_sort.clone()),
        rty::RefinedTypeVar::Free(j) => param_sorts.get(j.index()).cloned(),
        rty::RefinedTypeVar::Existential(k) => refinement.existentials.get(*k).cloned(),
    };
    let body = &refinement.body;
    let conjuncts = body
        .atoms
        .iter()
        .cloned()
        .map(chc::Formula::Atom)
        .chain(chc::conjuncts(&body.formula));
    let mut out = Vec::new();
    for conjunct in conjuncts {
        if !conjunct.fv().all(keep) {
            continue;
        }
        out.extend(chc::instances(
            &conjunct,
            &var_sort,
            head,
            MAX_INSTANCES_PER_CONJUNCT,
        ));
    }
    out
}

fn type_invariant_atom<V>(pred: &chc::Pred, term: chc::Term<V>) -> chc::Formula<V> {
    chc::Formula::Atom(chc::Atom::new(pred.clone(), vec![term]))
}
