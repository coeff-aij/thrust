//! Trait objects (`&dyn Tr`, `&mut dyn Tr`, `Box<dyn Tr>`).
//!
//! A trait object is an existential package, `∃T. T` with `T: Tr` and the impl's vtable as the
//! dictionary (Mitchell and Plotkin; Läufer). Its model is opaque: the unsize coercion packs a
//! value into a fresh opaque one, requires the value's type invariant, and checks every vtable
//! method of the impl against the trait's contract, and a call through the vtable takes the
//! trait's contract at `Self = dyn Tr`. That contract holds of every impl the call may reach,
//! under the invariant checked at packing, when it does not mention `self` or `Self`, whose model
//! the opaque value does not have; a contract that does is rejected at the call.

use rustc_middle::mir::Operand;
use rustc_middle::ty::{self as mir_ty};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{Analyzer, ResolvedCallable};
use crate::analyze;
use crate::chc;
use crate::refine::{PlaceType, PlaceTypeBuilder, Var};
use crate::rty::{self, Subtyping as _};

/// The type a pointer type (`&T`, `&mut T`, `Box<T>`) points to.
fn pointee<'tcx>(ty: mir_ty::Ty<'tcx>) -> Option<mir_ty::Ty<'tcx>> {
    ty.builtin_deref(true).or_else(|| ty.boxed_ty())
}

/// The trait object `ty` points to, if it is a pointer to one.
pub(super) fn dyn_pointee<'tcx>(ty: mir_ty::Ty<'tcx>) -> Option<mir_ty::Ty<'tcx>> {
    pointee(ty).filter(|ty| ty.is_trait())
}

/// The trait objects that occur in `ty`.
fn trait_objects<'tcx>(ty: mir_ty::Ty<'tcx>) -> Vec<mir_ty::Ty<'tcx>> {
    ty.walk()
        .filter_map(|arg| arg.as_type())
        .filter(|ty| ty.is_trait())
        .collect()
}

/// Whether the formula function `def_id` of a trait's contract mentions the receiver or `Self`:
/// it uses its parameter `self_` (the receiver's model, which a `Model` supertrait may have
/// normalized to a concrete type), or an expression, closures' bodies included, has a type or
/// generic arguments naming `Self` (a closure's own type, which carries its parent's `Self`, is
/// not looked into).
/// Read before instantiation: at `Self = dyn Tr` the receiver's model is single-valued and folds
/// to a constant.
fn formula_names_self(tcx: mir_ty::TyCtxt<'_>, def_id: LocalDefId) -> bool {
    struct Finder<'a, 'tcx> {
        tcx: mir_ty::TyCtxt<'tcx>,
        typeck: &'a mir_ty::TypeckResults<'tcx>,
        receiver: Option<rustc_hir::HirId>,
        found: bool,
    }
    fn names_self(ty: mir_ty::Ty<'_>) -> bool {
        let mut walker = ty.walk();
        while let Some(arg) = walker.next() {
            let mir_ty::GenericArgKind::Type(ty) = arg.kind() else {
                continue;
            };
            match ty.kind() {
                mir_ty::TyKind::Closure(..) => walker.skip_current_subtree(),
                mir_ty::TyKind::Param(param) if param.name == rustc_span::symbol::kw::SelfUpper => {
                    return true
                }
                _ => {}
            }
        }
        false
    }
    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for Finder<'_, 'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

        fn maybe_tcx(&mut self) -> mir_ty::TyCtxt<'tcx> {
            self.tcx
        }

        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(None, path)) = expr.kind {
                if let rustc_hir::def::Res::Local(id) = path.res {
                    self.found |= Some(id) == self.receiver;
                }
            }
            let ty_names_self = self
                .typeck
                .node_type_opt(expr.hir_id)
                .is_some_and(names_self);
            let args_name_self = self
                .typeck
                .node_args_opt(expr.hir_id)
                .is_some_and(|args| args.types().any(names_self));
            self.found |= ty_names_self || args_name_self;
            rustc_hir::intravisit::walk_expr(self, expr);
        }
    }
    let body = tcx.hir_body_owned_by(def_id);
    let receiver = body.params.iter().find_map(|param| match param.pat.kind {
        rustc_hir::PatKind::Binding(_, hir_id, ident, _) if ident.name.as_str() == "self_" => {
            Some(hir_id)
        }
        _ => None,
    });
    let mut finder = Finder {
        tcx,
        typeck: tcx.typeck(def_id),
        receiver,
        found: false,
    };
    rustc_hir::intravisit::Visitor::visit_expr(&mut finder, body.value);
    finder.found
}

/// The principal trait of the trait object `ty`.
fn principal_def_id(ty: mir_ty::Ty<'_>) -> Option<DefId> {
    let mir_ty::TyKind::Dynamic(preds, ..) = ty.kind() else {
        unreachable!("not a trait object: {ty:?}");
    };
    preds.principal_def_id()
}

impl<'tcx, 'ctx> Analyzer<'tcx, 'ctx> {
    /// Where a diagnostic is: the body analyzed, and the function it is analyzed for when that is
    /// another one (a generic body at an instance).
    fn site(&self) -> String {
        let body = self.local_def_id.to_def_id();
        let owner = self.type_builder.owner_fn_id();
        if body == owner {
            format!("`{}`", self.tcx.def_path_str(body))
        } else {
            format!(
                "`{}` (analyzed for `{}`)",
                self.tcx.def_path_str(body),
                self.tcx.def_path_str(owner)
            )
        }
    }

    /// Stops at an unsize coercion from `source_ty` to `ty` that makes a trait object other than
    /// `&dyn Tr`, `&mut dyn Tr` or `Box<dyn Tr>` (`Rc<dyn Tr>`, a `CoerceUnsized` struct), which
    /// would skip the checks of the coercion. One that keeps the trait objects of the source
    /// (`&[&dyn Tr; 1]` to `&[&dyn Tr]`) makes none.
    pub(super) fn check_other_unsize(&self, source_ty: mir_ty::Ty<'tcx>, ty: mir_ty::Ty<'tcx>) {
        let source = trait_objects(source_ty);
        if trait_objects(ty)
            .iter()
            .all(|dyn_ty| source.contains(dyn_ty))
        {
            return;
        }
        self.tcx.dcx().fatal(format!(
            "a coercion from `{source_ty}` to `{ty}` in {} is not supported: trait objects are made \
             only as `&dyn`, `&mut dyn` or `Box<dyn>`",
            self.site(),
        ));
    }

    /// `operand` coerced to `ty`, a pointer to the trait object `dyn_ty`: a fresh opaque value.
    /// The operand is moved, so a `&mut` operand's prophecy stays unresolved and the lender's
    /// value after the borrow is unknown, as after a call that leaves it unconstrained.
    pub(super) fn unsize_to_dyn(
        &mut self,
        operand: Operand<'tcx>,
        ty: mir_ty::Ty<'tcx>,
        dyn_ty: mir_ty::Ty<'tcx>,
    ) -> PlaceType {
        let source_ty = operand.ty(&self.local_decls, self.tcx);
        let hidden_ty = pointee(source_ty).expect("unsize cast from a pointer");
        let source = self.operand_type(operand);
        if hidden_ty.is_trait() {
            self.check_auto_trait_drop(hidden_ty, dyn_ty);
        } else {
            let owner = self.type_builder.owner_fn_id();
            let invariant = self
                .ctx
                .type_invariant_instance(hidden_ty, owner)
                .map(|instance| {
                    chc::Pred::from(self.ctx.predicate_with_args(
                        instance.def_id(),
                        instance.args,
                        owner,
                    ))
                });
            self.check_vtable_methods(hidden_ty, dyn_ty, invariant.is_some());
            if let Some(pred) = invariant {
                self.require_hidden_invariant(source_ty, pred, source.clone());
            }
        }
        let expected_ty = self.type_builder.build(ty).vacuous().ty;
        let mut builder = PlaceTypeBuilder::default();
        let _ = builder.subsume(source);
        let term = if expected_ty.is_mut() {
            chc::Term::mut_(chc::Term::null(), chc::Term::null())
        } else {
            chc::Term::box_(chc::Term::null())
        };
        builder.build(expected_ty, term)
    }

    /// Stops at a coercion between trait objects unless it only drops auto traits
    /// (`dyn Tr + Sync` to `dyn Tr`), which keeps the vtable.
    fn check_auto_trait_drop(&self, source_dyn: mir_ty::Ty<'tcx>, dyn_ty: mir_ty::Ty<'tcx>) {
        if principal_def_id(source_dyn) == principal_def_id(dyn_ty) {
            return;
        }
        self.tcx.dcx().fatal(format!(
            "a trait object coerced to one of another trait (`{source_dyn}` to `{dyn_ty}` in {}) \
             is not supported",
            self.site(),
        ));
    }

    /// Requires the type invariant `pred` of the value packed into a trait object, as a parameter
    /// of type `&T`, `&mut T` or `Box<T>` requires it: the impl's methods are checked assuming
    /// it, and a call through the trait object does not state it.
    fn require_hidden_invariant(
        &mut self,
        source_ty: mir_ty::Ty<'tcx>,
        pred: chc::Pred,
        source: PlaceType,
    ) {
        let value = chc::Term::var(rty::RefinedTypeVar::Value);
        let current = if source_ty.is_mutable_ptr() {
            value.mut_current()
        } else {
            value.box_current()
        };
        let invariant = chc::Formula::Atom(chc::Atom::new(pred, vec![current]));
        let expected = rty::RefinedType::<Var>::new(source.ty.clone(), invariant.into());
        let got: rty::RefinedType<Var> = source.into();
        let clauses = self.env.relate_sub_refined_type(&got, &expected);
        self.ctx.extend_clauses(clauses);
    }

    /// Requests each method of `hidden_ty`'s impl of `dyn_ty`'s trait and its supertraits that a
    /// call through the vtable may reach, a method with a written trait contract, so that its body
    /// is checked against that contract.
    fn check_vtable_methods(
        &mut self,
        hidden_ty: mir_ty::Ty<'tcx>,
        dyn_ty: mir_ty::Ty<'tcx>,
        has_invariant: bool,
    ) {
        let mir_ty::TyKind::Dynamic(preds, ..) = dyn_ty.kind() else {
            unreachable!("not a trait object: {dyn_ty:?}");
        };
        let Some(principal) = preds.principal() else {
            return;
        };
        let trait_ref = self
            .tcx
            .instantiate_bound_regions_with_erased(principal.with_self_ty(self.tcx, hidden_ty));
        let mut pending = vec![trait_ref];
        let mut seen = std::collections::HashSet::new();
        while let Some(trait_ref) = pending.pop() {
            if !seen.insert(trait_ref) {
                continue;
            }
            self.check_dyn_trait(trait_ref.def_id, dyn_ty);
            for method in self
                .tcx
                .associated_items(trait_ref.def_id)
                .in_definition_order()
            {
                if !method.is_fn()
                    || !rustc_trait_selection::traits::is_vtable_safe_method(
                        self.tcx,
                        trait_ref.def_id,
                        *method,
                    )
                    || !self.ctx.trait_method_contract_written(method.def_id)
                {
                    continue;
                }
                let args = mir_ty::GenericArgs::for_item(self.tcx, method.def_id, |param, _| {
                    trait_ref
                        .args
                        .get(param.index as usize)
                        .copied()
                        .unwrap_or_else(|| self.tcx.lifetimes.re_erased.into())
                });
                self.request_vtable_method(method.def_id, args, dyn_ty, has_invariant);
            }
            pending.extend(analyze::extern_spec::supertrait_bounds(self.tcx, trait_ref));
        }
    }

    /// Requests the type of the body the vtable holds for the trait method `def_id` at `args`
    /// (`Self` the packed type), so that it is checked against the trait's contract.
    fn request_vtable_method(
        &mut self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        dyn_ty: mir_ty::Ty<'tcx>,
        has_invariant: bool,
    ) {
        // At a type parameter (a body verified once over it) the impl is not known here. It is
        // requested where the body is analyzed at an instance, which a crate with an invariant
        // does at each instance a call reaches; otherwise each impl of the crate is checked
        // against the trait's contract on its own.
        let Some(instance) = mir_ty::Instance::try_resolve(self.tcx, self.typing_env, def_id, args)
            .ok()
            .flatten()
        else {
            return;
        };
        let resolved = instance.def_id();
        if analyze::is_ignored_crate_fn(self.tcx, resolved) {
            analyze::fatal_ignored_call(self.tcx, resolved, instance.args);
        }
        if has_invariant {
            self.check_invariant_kept(def_id, args, resolved, instance.args, dyn_ty);
        }
        let owner = self.type_builder.owner_fn_id();
        let _ = self.ctx.def_ty_with_args(resolved, instance.args, owner);
    }

    /// Stops unless the body `resolved` the vtable holds for the trait method `def_id`, if it
    /// takes `&mut self`, ensures the type invariant of the receiver's final value, as its
    /// contract does unless the receiver is `#[thrust::open_inv]` or its borrow may outlive the
    /// call ([`analyze::local_def::Analyzer::ensures_final_invariant`]). A trait's default body
    /// is analyzed at the packed type, as generic bodies are in a crate with an invariant, so its
    /// contract there has the conjunct too. Calls through the trait object assume the invariant
    /// of the packed value, which only these bodies change.
    fn check_invariant_kept(
        &mut self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        resolved: DefId,
        resolved_args: mir_ty::GenericArgsRef<'tcx>,
        dyn_ty: mir_ty::Ty<'tcx>,
    ) {
        let tcx = self.tcx;
        let hidden_ty = args.type_at(0);
        let receiver = tcx.fn_sig(def_id).skip_binder().inputs().skip_binder()[0];
        if !receiver.is_mutable_ptr() {
            return;
        }
        let (contract_def, contract_args) = if self.ctx.has_own_impl_contract(resolved) {
            (resolved, resolved_args)
        } else {
            (def_id, args)
        };
        let owner = self.type_builder.owner_fn_id();
        let kept = self
            .ctx
            .ensures_final_invariant_at(contract_def, contract_args, owner, 0);
        if kept {
            return;
        }
        tcx.dcx().fatal(format!(
            "`{hidden_ty}` packed into `{dyn_ty}` in {} is not supported: its invariant is not \
             ensured after `{}`, whose `&mut self` is `#[thrust::open_inv]` or may \
             outlive the call, and calls through the trait object \
             assume it",
            self.site(),
            tcx.def_path_str(resolved),
        ));
    }

    /// Stops unless the trait `trait_def_id`, reached through the trait object `dyn_ty`, is a
    /// trait of the crate that declares no law, logic function or predicate: those would be
    /// assumed of `dyn_ty`, which no impl proves them of (Creusot's `unsound_dyn`).
    fn check_dyn_trait(&self, trait_def_id: DefId, dyn_ty: mir_ty::Ty<'tcx>) {
        let tcx = self.tcx;
        let site = self.site();
        let trait_name = tcx.def_path_str(trait_def_id);
        if !trait_def_id.is_local() {
            tcx.dcx().fatal(format!(
                "`{dyn_ty}` in {site}: trait objects are supported only of the crate's own \
                 traits, and `{trait_name}` is not one"
            ));
        }
        if self.has_model_supertrait(trait_def_id) {
            tcx.dcx().fatal(format!(
                "`{dyn_ty}` in {site}: trait objects of a trait with `thrust_models::Model` as a \
                 supertrait are not supported: its contracts would read the receiver at the \
                 impl's model, while a trait object's is opaque"
            ));
        }
        let logic_paths = [
            analyze::annot::law_path(),
            analyze::annot::logic_path(),
            analyze::annot::predicate_path(),
        ];
        let logic_item = tcx
            .associated_items(trait_def_id)
            .in_definition_order()
            .find(|item| {
                logic_paths
                    .iter()
                    .any(|path| tcx.get_attrs_by_path(item.def_id, path).next().is_some())
            });
        if let Some(item) = logic_item {
            tcx.dcx().fatal(format!(
                "`{dyn_ty}` in {site}: trait objects of a trait with laws, logic functions or \
                 predicates are not supported, and `{trait_name}` declares `{}`",
                tcx.def_path_str(item.def_id),
            ));
        }
    }

    /// Whether `trait_def_id` has `thrust_models::Model` among its supertraits.
    fn has_model_supertrait(&self, trait_def_id: DefId) -> bool {
        let Some(model_ty) = self.ctx.def_ids().model_ty() else {
            return false;
        };
        let model_trait = self.tcx.parent(model_ty);
        let mut pending = vec![trait_def_id];
        let mut seen = std::collections::HashSet::new();
        while let Some(def_id) = pending.pop() {
            if def_id == model_trait {
                return true;
            }
            if !seen.insert(def_id) {
                continue;
            }
            pending.extend(
                self.tcx
                    .explicit_super_predicates_of(def_id)
                    .skip_binder()
                    .iter()
                    .filter_map(|(clause, _)| clause.as_trait_clause())
                    .map(|pred| pred.def_id()),
            );
        }
        false
    }

    /// The trait-object checks of a call of `def_id` at `args`, which resolves to `resolved`: a
    /// call through a vtable (the instance is the trait method itself at a trait object) needs a
    /// contract that does not mention `self` or `Self`, and no other type argument, of the call
    /// or of the impl it resolves to, is a trait object. A trait method's `Self` may be a trait
    /// object with an impl of its own (`impl Tr for dyn Other`), which is an ordinary impl.
    pub(super) fn check_dyn_instance(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        resolved: &ResolvedCallable<'tcx>,
    ) {
        let is_trait_method = self.tcx.trait_of_assoc(def_id).is_some();
        let self_is_dyn = is_trait_method && args.type_at(0).is_trait();
        match resolved {
            ResolvedCallable::Concrete(resolved_def_id, _)
                if self_is_dyn && *resolved_def_id == def_id =>
            {
                self.check_dyn_call(def_id, args);
                self.check_no_dyn_type_arg(def_id, args, 1);
            }
            ResolvedCallable::Concrete(resolved_def_id, resolved_args)
                if *resolved_def_id != def_id =>
            {
                self.check_no_dyn_type_arg(def_id, args, usize::from(is_trait_method));
                self.check_no_dyn_type_arg(*resolved_def_id, resolved_args, 0);
            }
            _ => self.check_no_dyn_type_arg(def_id, args, usize::from(is_trait_method)),
        }
    }

    /// Stops at a call of the trait method `def_id` through the trait object `args[0]` unless
    /// the trait gives the method a written contract that does not mention `self` or `Self`.
    fn check_dyn_call(&self, def_id: DefId, args: mir_ty::GenericArgsRef<'tcx>) {
        let tcx = self.tcx;
        let dyn_ty = args.type_at(0);
        let trait_def_id = tcx.trait_of_assoc(def_id).expect("a trait method");
        self.check_dyn_trait(trait_def_id, dyn_ty);
        let site = self.site();
        let method = tcx.def_path_str(def_id);
        if !self.ctx.trait_method_contract_written(def_id) {
            tcx.dcx().fatal(format!(
                "`{method}` is called through `{dyn_ty}` in {site}, but has no contract on the \
                 trait: a call through a trait object takes the trait's contract"
            ));
        }
        let formulas = self.ctx.written_contract_formulas(def_id);
        if formulas
            .iter()
            .any(|formula| formula_names_self(tcx, *formula))
        {
            tcx.dcx().fatal(format!(
                "`{method}` is called through `{dyn_ty}` in {site}, but its contract mentions \
                 `self` or `Self`, whose model a trait object does not have"
            ));
        }
    }

    /// Stops at a call that instantiates a type parameter with a trait object (`g::<dyn Tr>`, or
    /// an impl for `Box<T>` at `T = dyn Tr`): the callee's contract and the laws of its bounds
    /// would be assumed of `dyn Tr`. The type arguments from `from` on are checked.
    fn check_no_dyn_type_arg(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
        from: usize,
    ) {
        let Some(dyn_ty) = args.types().skip(from).find(|ty| ty.is_trait()) else {
            return;
        };
        self.tcx.dcx().fatal(format!(
            "`{}` in {} instantiates a type parameter with the trait object `{dyn_ty}`, which is \
             not supported",
            self.tcx.def_path_str_with_args(def_id, args),
            self.site(),
        ));
    }
}
