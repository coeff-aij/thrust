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
//!   the hand-over; an entry the walk finds into a closure no call handed over stops.

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
    /// Closures, likewise.
    pub closures: Vec<(mir_ty::Instance<'tcx>, mir_ty::Instance<'tcx>)>,
    /// The analyzed instances the walk reached, whose hand-overs cover the closures.
    pub analyzed: Vec<mir_ty::Instance<'tcx>>,
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

    pub fn record_handover(&mut self, owner: DefId, handed_over: HandedOver) {
        self.handovers.push((owner, handed_over));
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
            let key = (root, item_analyzed(root));
            if seen.insert(key) {
                pending.push_back(key);
            }
        }
        let mut entries = Entries::default();
        while let Some((instance, analyzed)) = pending.pop_front() {
            if analyzed {
                entries.analyzed.push(instance);
            }
            if !self.runs_body(instance) {
                continue;
            }
            let stated = (!analyzed).then(|| {
                self.contract_of(instance.def_id(), instance.args)
                    .map(|(contract_def_id, _)| self.stated_pres(contract_def_id))
                    .unwrap_or_default()
            });
            for callee in self.callees(instance) {
                let callee_analyzed = match callee.def {
                    mir_ty::InstanceKind::ClosureOnceShim { .. }
                    | mir_ty::InstanceKind::FnPtrShim(..) => analyzed,
                    _ => item_analyzed(callee),
                };
                let key = (callee, callee_analyzed);
                if seen.insert(key) {
                    pending.push_back(key);
                }
                let Some(stated) = stated.as_ref().filter(|_| callee_analyzed) else {
                    continue;
                };
                let callee_def_id = callee.def_id();
                if Some(callee_def_id) == entry_fn {
                    continue;
                }
                if self.tcx.is_closure_like(callee_def_id) {
                    entries.closures.push((callee, instance));
                } else if !self.names_fn_item(stated, callee_def_id) {
                    entries.items.push((callee, instance));
                }
            }
        }
        entries
    }

    /// The contract of the function `instance` runs, at its generic arguments.
    pub fn entered_fn_ty(&mut self, instance: mir_ty::Instance<'tcx>) -> Option<rty::FunctionType> {
        let def_id = instance.def_id();
        let generic = self
            .tcx
            .generics_of(def_id)
            .requires_monomorphization(self.tcx);
        let def_ty = if generic {
            self.def_ty_with_args(def_id, instance.args, def_id)?
        } else {
            self.concrete_def_ty(def_id)?.clone()
        };
        def_ty.ty.as_function().cloned()
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

    /// The closures the hand-overs of the analyzed instances `analyzed` cover, by def id.
    pub fn handed_over_closures(&self, analyzed: &[mir_ty::Instance<'tcx>]) -> HashSet<DefId> {
        let mut covered = HashSet::new();
        for instance in analyzed {
            let owner = instance.def_id();
            for (_, handed_over) in self.handovers.iter().filter(|(o, _)| *o == owner) {
                match *handed_over {
                    HandedOver::Closure(def_id) => {
                        covered.insert(def_id);
                    }
                    HandedOver::Param(param_def_id) => {
                        let generics = self.tcx.generics_of(owner);
                        let Some(&index) = generics.param_def_id_to_index.get(&param_def_id) else {
                            continue;
                        };
                        let Some(ty) = instance.args.get(index as usize).and_then(|a| a.as_type())
                        else {
                            continue;
                        };
                        covered.extend(ty.walk().filter_map(|arg| {
                            match arg.as_type().map(|ty| *ty.kind()) {
                                Some(mir_ty::TyKind::Closure(def_id, _)) => Some(def_id),
                                _ => None,
                            }
                        }));
                    }
                }
            }
        }
        covered
    }
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
