//! Items whose contract Thrust infers, entered from code Thrust does not analyze.
//!
//! The precondition of an item without a written contract is inferred from the calls Thrust
//! analyzes. Code Thrust does not analyze (a trusted body, a function outside
//! `THRUST_VERIFY_ONLY` trusted for its contract, std code) may run such an item too, and its
//! calls add nothing to that precondition. At each such entry the precondition is fixed instead,
//! as Creusot, Verus, Prusti and Dafny fix an omitted `requires` and Flux an unrefined `Fn` bound:
//! to the `pre!` the entering contract states of the item, and otherwise to `true` for every
//! argument.
//!
//! - A function or method run by name or through a bound has only its parameters as state; its
//!   entry is an edge of the walk below, answered by a clause that its precondition holds of every
//!   argument ([`Analyzer::accepts_every_argument`]).
//! - A closure is handed over as a value, with captures the walk does not see. Its obligation is
//!   stated at the analyzed call that hands it over (`basic_block::closure_escape`), which records
//!   the hand-over; an entry the walk finds into a closure on a path where the analyzed call
//!   that led into unanalyzed code did not hand it over stops, whatever other calls hand over.

use std::collections::{HashSet, VecDeque};

use rustc_middle::ty::{self as mir_ty};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::Symbol;

use crate::analyze;
use crate::chc;
use crate::rty;

/// A closure an analyzed body hands over to code Thrust does not analyze.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HandedOver {
    /// The closure itself.
    Closure(DefId),
    /// Whatever closure the body's type parameter (by its def id) is instantiated with.
    Param(DefId),
}

/// What a `requires` names the precondition of with `pre!`.
#[derive(Debug, Clone, Default)]
pub struct StatedPres {
    /// The type parameters a `pre!` receiver's type mentions, by name.
    params: HashSet<Symbol>,
    /// The functions named as a `pre!` receiver.
    fn_items: HashSet<DefId>,
}

impl StatedPres {
    pub fn names_param(&self, name: Symbol) -> bool {
        self.params.contains(&name)
    }
}

/// The entries of the walk from code Thrust does not analyze into crate items it analyzes.
#[derive(Debug, Default)]
pub struct Entries<'tcx> {
    /// Functions and methods, with the unanalyzed instance each is entered from.
    pub items: Vec<(mir_ty::Instance<'tcx>, mir_ty::Instance<'tcx>)>,
    /// Closures entered on a path on which no analyzed call handed them over, likewise.
    pub unhanded_closures: Vec<(mir_ty::Instance<'tcx>, mir_ty::Instance<'tcx>)>,
    /// The closure and function pointer types an entered function returns, or can store
    /// behind a `&mut` argument, to the unanalyzed instance it is entered from: values the
    /// walk does not see handed over.
    pub escaping: Vec<(
        mir_ty::Instance<'tcx>,
        mir_ty::Instance<'tcx>,
        mir_ty::Ty<'tcx>,
    )>,
}

/// An instance on the walk: whether its body is analyzed, and, for one that is not, the
/// closures the analyzed call that led into unanalyzed code on its path handed over.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Node<'tcx> {
    instance: mir_ty::Instance<'tcx>,
    analyzed: bool,
    /// Sorted by [`def_order`], without repeats.
    handed_over: Vec<DefId>,
}

impl<'tcx> analyze::Analyzer<'tcx> {
    /// Records the fn-like defs whose bodies are trusted rather than analyzed.
    pub fn set_trusted_bodies(&mut self, trusted: HashSet<LocalDefId>) {
        self.trusted_bodies = trusted;
    }

    /// Whether `def_id` is a crate function whose body is trusted rather than analyzed.
    pub fn is_trusted_body(&self, def_id: DefId) -> bool {
        def_id
            .as_local()
            .is_some_and(|local| self.trusted_bodies.contains(&local))
    }

    /// Whether `def_id` is a crate function with a written `requires`.
    pub fn has_written_requires(&self, def_id: DefId) -> bool {
        def_id.as_local().is_some_and(|local| {
            self.extract_path_with_attr(local, &analyze::annot::requires_path_path())
                .is_some()
        })
    }

    /// Records that the analyzed body `owner` hands `handed_over` to `callee` at a call.
    pub fn record_handover(&mut self, owner: DefId, callee: DefId, handed_over: HandedOver) {
        self.handovers.push((owner, callee, handed_over));
    }

    /// What the `requires` of `contract_def_id` names the precondition of: the type parameters
    /// and functions of each `pre!` receiver (`f`, `&f`, a `Closure<F>` or `Mut<Closure<F>>`
    /// state, a function item).
    pub fn stated_pres(&self, contract_def_id: DefId) -> StatedPres {
        let mut stated = StatedPres::default();
        let Some(local) = contract_def_id.as_local() else {
            return stated;
        };
        let Some(formula_def_id) = self
            .extract_path_with_attr(local, &analyze::annot::requires_path_path())
            .and_then(DefId::as_local)
        else {
            return stated;
        };
        let Some(closure_precondition) = self.def_ids().closure_precondition() else {
            return stated;
        };
        let typeck = self.tcx.typeck(formula_def_id);
        let mut receivers = Vec::new();
        let body = self.tcx.hir_body_owned_by(formula_def_id);
        collect_pre_receivers(
            self.tcx,
            typeck,
            closure_precondition,
            body.value,
            &mut receivers,
        );
        for ty in receivers {
            for arg in ty.walk() {
                match arg.as_type().map(|ty| *ty.kind()) {
                    Some(mir_ty::TyKind::Param(param)) => {
                        stated.params.insert(param.name);
                    }
                    Some(mir_ty::TyKind::FnDef(def_id, _)) => {
                        stated.fn_items.insert(def_id);
                    }
                    _ => {}
                }
            }
        }
        stated
    }

    /// Whether `stated` names the precondition of `callee`, or of the trait method it implements.
    fn names_fn_item(&self, stated: &StatedPres, callee: DefId) -> bool {
        let trait_item = self
            .tcx
            .opt_associated_item(callee)
            .and_then(|item| item.trait_item_def_id);
        stated.fn_items.contains(&callee)
            || trait_item.is_some_and(|item| stated.fn_items.contains(&item))
    }

    /// The contract a call of `def_id` at `args` from an analyzed body is checked against when
    /// the function that runs is not analyzed, with that contract's generic arguments: a
    /// trusted crate function's, or the extern spec of a std function. `None` when the function
    /// is analyzed, or has no such contract.
    pub fn unanalyzed_contract(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        let analyzed = def_id.is_local()
            && (!self.is_trusted_body(def_id) || self.tcx.is_closure_like(def_id));
        if analyzed {
            return None;
        }
        self.contract_of(def_id, args)
    }

    /// The def whose annotations give `def_id` its contract at `args`, with its generic
    /// arguments: `def_id` itself, or the extern-spec wrapper that carries the contract of a std
    /// function or of a trusted generic one.
    fn contract_of(
        &self,
        def_id: DefId,
        args: mir_ty::GenericArgsRef<'tcx>,
    ) -> Option<(DefId, mir_ty::GenericArgsRef<'tcx>)> {
        let analyze::DefTy::Deferred(specs) = self.defs.get(&def_id)? else {
            return Some((def_id, args));
        };
        specs.iter().find_map(|spec| {
            let spec_def_id = spec.local_def_id.to_def_id();
            let Some(target_args) = spec.target_args else {
                return Some((spec_def_id, args));
            };
            let bound = analyze::extern_spec::bind_spec_args(
                self.tcx,
                spec.local_def_id,
                target_args,
                args,
            )?;
            Some((spec_def_id, bound))
        })
    }

    /// Walks the instances the verified functions can run, as
    /// [`analyze::Analyzer::stop_ignored_reached`] does from the same roots, and returns the
    /// edges from an instance whose body Thrust does not analyze into a crate function it
    /// analyzes: a closure, or a function or method whose precondition the entering contract
    /// does not name with `pre!`. A non-local instance is not analyzed; a closure call shim takes
    /// the analyzed-ness of the instance it is reached from, since a call Thrust types through the
    /// closure's contract goes through it; other shims are not analyzed. The entry function is
    /// left out: its precondition is required of every argument already
    /// (`crate_::Analyzer::assert_callable_entry`).
    pub fn unanalyzed_entries(
        &self,
        roots: Vec<mir_ty::Instance<'tcx>>,
        is_analyzed: impl Fn(DefId) -> bool,
    ) -> Entries<'tcx> {
        let entry_fn = self.tcx.entry_fn(()).map(|(def_id, _)| def_id);
        let item_analyzed = |instance: mir_ty::Instance<'tcx>| match instance.def {
            mir_ty::InstanceKind::Item(def_id) => def_id.is_local() && is_analyzed(def_id),
            _ => false,
        };
        let mut seen = HashSet::new();
        let mut pending = VecDeque::new();
        for root in roots {
            let node = Node {
                instance: root,
                analyzed: item_analyzed(root),
                handed_over: Vec::new(),
            };
            if seen.insert(node.clone()) {
                pending.push_back(node);
            }
        }
        let mut entries = Entries::default();
        while let Some(node) = pending.pop_front() {
            let instance = node.instance;
            if !self.runs_body(instance) || self.nests_past_recursion_limit(instance) {
                continue;
            }
            let stated = (!node.analyzed).then(|| {
                self.contract_of(instance.def_id(), instance.args)
                    .map(|(contract_def_id, _)| self.stated_pres(contract_def_id))
                    .unwrap_or_default()
            });
            for callee in self.callees(instance) {
                let analyzed = match callee.def {
                    mir_ty::InstanceKind::ClosureOnceShim { .. }
                    | mir_ty::InstanceKind::FnPtrShim(..) => node.analyzed,
                    _ => item_analyzed(callee),
                };
                let handed_over = match (node.analyzed, analyzed) {
                    (_, true) => Vec::new(),
                    (true, false) => self.handed_over_at(instance, callee.def_id()),
                    (false, false) => node.handed_over.clone(),
                };
                let child = Node {
                    instance: callee,
                    analyzed,
                    handed_over,
                };
                if seen.insert(child.clone()) {
                    pending.push_back(child);
                }
                let Some(stated) = stated.as_ref().filter(|_| analyzed) else {
                    continue;
                };
                let callee_def_id = callee.def_id();
                if Some(callee_def_id) == entry_fn {
                    continue;
                }
                entries.escaping.extend(
                    self.escaping_callables(callee)
                        .into_iter()
                        .map(|ty| (callee, instance, ty)),
                );
                if self.tcx.is_closure_like(callee_def_id) {
                    if !node.handed_over.contains(&callee_def_id) {
                        entries.unhanded_closures.push((callee, instance));
                    }
                } else if !self.names_fn_item(stated, callee_def_id) {
                    entries.items.push((callee, instance));
                }
            }
        }
        entries
    }

    /// The closure and function pointer types in what `instance` returns and in the types
    /// behind a `&mut` among its parameters, the fields of structs and enums included.
    fn escaping_callables(&self, instance: mir_ty::Instance<'tcx>) -> Vec<mir_ty::Ty<'tcx>> {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let fn_ty = instance.ty(self.tcx, typing_env);
        let sig = match fn_ty.kind() {
            mir_ty::TyKind::Closure(_, args) => args.as_closure().sig(),
            mir_ty::TyKind::FnDef(..) => fn_ty.fn_sig(self.tcx),
            _ => return Vec::new(),
        };
        let sig = self.tcx.instantiate_bound_regions_with_erased(sig);
        let sig = self.tcx.normalize_erasing_regions(typing_env, sig);
        let written = sig.inputs().iter().copied().filter(|ty| {
            self.reachable_types(*ty).iter().any(|ty| {
                matches!(
                    ty.kind(),
                    mir_ty::TyKind::Ref(_, _, mir_ty::Mutability::Mut)
                )
            })
        });
        std::iter::once(sig.output())
            .chain(written)
            .flat_map(|ty| self.reachable_types(ty))
            .filter(|ty| {
                matches!(
                    ty.kind(),
                    mir_ty::TyKind::Closure(..) | mir_ty::TyKind::FnPtr(..)
                )
            })
            .collect()
    }

    /// The types a value of `ty` holds: its type arguments and the field types of the structs
    /// and enums in it, transitively. A closure's own arguments (its signature, its captures)
    /// are its own and not followed.
    fn reachable_types(&self, ty: mir_ty::Ty<'tcx>) -> Vec<mir_ty::Ty<'tcx>> {
        let typing_env = mir_ty::TypingEnv::fully_monomorphized();
        let mut seen = HashSet::new();
        let mut pending = vec![ty];
        let mut reached = Vec::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            let mut walker = ty.walk();
            while let Some(arg) = walker.next() {
                let Some(inner) = arg.as_type() else {
                    continue;
                };
                reached.push(inner);
                match inner.kind() {
                    mir_ty::TyKind::Closure(..) => walker.skip_current_subtree(),
                    mir_ty::TyKind::Adt(adt, args) => {
                        pending.extend(adt.all_fields().map(|field| {
                            self.tcx
                                .normalize_erasing_regions(typing_env, field.ty(self.tcx, args))
                        }));
                    }
                    _ => {}
                }
            }
        }
        reached
    }

    /// Whether the generic arguments of `instance` nest as deeply as the recursion limit, as
    /// those of a polymorphically recursive function do. Such an instance is not followed:
    /// rustc's collector stops at it, and so does `check_reused_instances` afterwards.
    fn nests_past_recursion_limit(&self, instance: mir_ty::Instance<'tcx>) -> bool {
        let limit = self.tcx.recursion_limit().0;
        instance
            .args
            .iter()
            .any(|arg| analyze::extern_spec::type_depth(arg) >= limit)
    }

    /// The contract of the function `instance` runs, at its generic arguments, when its
    /// precondition is inferred. A generic def's template tells before its body is analyzed at
    /// the instance.
    pub fn entered_inferred_fn_ty(
        &mut self,
        instance: mir_ty::Instance<'tcx>,
    ) -> Option<rty::FunctionType> {
        let def_id = instance.def_id();
        let template = self
            .concrete_def_ty(def_id)
            .and_then(|def_ty| def_ty.ty.as_function().cloned());
        if template
            .as_ref()
            .is_some_and(|fn_ty| !self.infers_precondition(fn_ty))
        {
            return None;
        }
        let generic = self
            .tcx
            .generics_of(def_id)
            .requires_monomorphization(self.tcx);
        let fn_ty = if generic {
            self.def_ty_with_args(def_id, instance.args, def_id)?
                .ty
                .as_function()
                .cloned()?
        } else {
            template?
        };
        self.infers_precondition(&fn_ty).then_some(fn_ty)
    }

    /// Whether the precondition of `fn_ty` is inferred: a parameter's refinement names an
    /// unknown, directly or through a predicate's definition.
    pub fn infers_precondition(&self, fn_ty: &rty::FunctionType) -> bool {
        fn_ty.params.iter().any(|param| {
            let reach = self.pred_var_reach(param);
            reach.found || reach.undefined
        })
    }

    /// The clauses that make the precondition of `fn_ty` hold of every argument.
    pub fn accepts_every_argument(fn_ty: &rty::FunctionType) -> Vec<chc::Clause> {
        let expected = fn_ty
            .params
            .iter()
            .map(|param| {
                rty::RefinedType::<rty::Closed>::unrefined(param.ty.clone().strip_refinement())
            })
            .collect();
        analyze::basic_block::relate_param_sub_types(
            fn_ty.params.clone(),
            &expected,
            &mut chc::ClauseBuilder::default(),
        )
    }

    /// The closures, by def id, that the analyzed instance `owner` hands over at its calls of
    /// `callee`.
    fn handed_over_at(&self, owner: mir_ty::Instance<'tcx>, callee: DefId) -> Vec<DefId> {
        let owner_def_id = owner.def_id();
        let mut handed_over = Vec::new();
        let recorded = self
            .handovers
            .iter()
            .filter(|(o, c, _)| *o == owner_def_id && *c == callee);
        for (_, _, closure) in recorded {
            match *closure {
                HandedOver::Closure(def_id) => {
                    handed_over.push(def_id);
                }
                HandedOver::Param(param_def_id) => {
                    let generics = self.tcx.generics_of(owner_def_id);
                    let Some(&index) = generics.param_def_id_to_index.get(&param_def_id) else {
                        continue;
                    };
                    let Some(ty) = owner.args.get(index as usize).and_then(|a| a.as_type()) else {
                        continue;
                    };
                    handed_over.extend(ty.walk().filter_map(|arg| {
                        match arg.as_type().map(|ty| *ty.kind()) {
                            Some(mir_ty::TyKind::Closure(def_id, _)) => Some(def_id),
                            _ => None,
                        }
                    }));
                }
            }
        }
        handed_over.sort_by_key(|def_id| def_order(*def_id));
        handed_over.dedup();
        handed_over
    }
}

/// An order of def ids within one compilation.
fn def_order(def_id: DefId) -> (u32, u32) {
    (def_id.krate.as_u32(), def_id.index.as_u32())
}

/// The type of the receiver of each `pre!` (a call of `closure_precondition`) in `expr`, closures
/// in it included.
fn collect_pre_receivers<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    typeck: &'tcx mir_ty::TypeckResults<'tcx>,
    closure_precondition: DefId,
    expr: &'tcx rustc_hir::Expr<'tcx>,
    receivers: &mut Vec<mir_ty::Ty<'tcx>>,
) {
    struct Collector<'a, 'tcx> {
        tcx: mir_ty::TyCtxt<'tcx>,
        typeck: &'tcx mir_ty::TypeckResults<'tcx>,
        closure_precondition: DefId,
        receivers: &'a mut Vec<mir_ty::Ty<'tcx>>,
    }
    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for Collector<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            match expr.kind {
                rustc_hir::ExprKind::Call(func, [receiver, ..]) => {
                    if let rustc_hir::ExprKind::Path(qpath) = &func.kind {
                        let res = self.typeck.qpath_res(qpath, func.hir_id);
                        if res.opt_def_id() == Some(self.closure_precondition) {
                            self.receivers.push(self.typeck.expr_ty(receiver));
                        }
                    }
                }
                rustc_hir::ExprKind::Closure(closure) => {
                    self.visit_expr(self.tcx.hir_body(closure.body).value);
                }
                _ => {}
            }
            rustc_hir::intravisit::walk_expr(self, expr);
        }
    }
    let mut collector = Collector {
        tcx,
        typeck,
        closure_precondition,
        receivers,
    };
    rustc_hir::intravisit::Visitor::visit_expr(&mut collector, expr);
}
