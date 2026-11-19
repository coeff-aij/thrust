//! Reusing the generic analysis of a def at an instance whose type arguments are `FnMut`
//! closures, and the obligations that reuse records.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze::{closure_hist_inv, Analyzer, DefTy};
use crate::chc;
use crate::rty;

/// What the reuse of generic analyses at `FnMut` instances records in the [`Analyzer`].
#[derive(Clone, Default)]
pub(super) struct FnMutReuse {
    /// The clauses [`closure_hist_inv::instance_obligations`] gave for the instances at an `FnMut`
    /// closure that use a generic def's contract as instantiated: the `hist_inv!` laws and the
    /// precondition clauses, pushed by [`Analyzer::emit_fn_mut_instance_obligations`].
    fn_mut_instance_obligations: Rc<RefCell<FnMutInstanceObligations>>,
    /// See [`Analyzer::record_hist_inv_specified_params`].
    hist_inv_specified_params: Rc<RefCell<HashSet<DefId>>>,
    /// See [`Analyzer::record_once_post_param`].
    once_post_params: Rc<RefCell<HashSet<DefId>>>,
}

/// See [`Analyzer::reuse_fn_mut_generic`].
#[derive(Default)]
struct FnMutInstanceObligations {
    laws: Vec<chc::Clause>,
    pre: Vec<chc::Clause>,
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
pub(super) fn has_fn_mut_closure(generic_args: mir_ty::GenericArgsRef<'_>) -> bool {
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

impl<'tcx> Analyzer<'tcx> {
    /// Whether an instance of the generic def `def_id` at `generic_args`, which has an `FnMut`
    /// closure among them or is an instance of a `hist_inv!`-specified `FnMut`-bounded def, can use
    /// its contract as instantiated rather than analyzing the body again. The generic analysis
    /// stands for the instance once the closures obey what it assumed of their type parameters;
    /// those obligations are recorded here. It requires:
    ///
    /// - the def not to state `post!` of a state held as a value
    ///   ([`Analyzer::record_once_post_param`]);
    /// - each type argument that is an `FnMut` closure to sit at one of the def's `FnMut`-bounded
    ///   parameters;
    /// - no unknown reachable from the contract, and a known contract for each closure.
    ///
    /// A def with an `FnMut`-bounded parameter that is not `hist_inv!`-specified has no generic
    /// analysis and never comes here ([`Analyzer::is_checked_per_instance`]).
    pub(super) fn reuse_fn_mut_generic(
        &mut self,
        def_id: DefId,
        expected: &rty::RefinedType,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> bool {
        let callee_bounded = fn_mut_bounded_params(self.tcx, def_id);
        let once_post_params = self.fn_mut_reuse.once_post_params.borrow();
        if let Some(param) = callee_bounded
            .iter()
            .find(|param| once_post_params.contains(param))
        {
            tracing::info!(
                ?param,
                "FnMut instance analyzed again: a specification states post! of a state held as a value"
            );
            return false;
        }
        drop(once_post_params);
        let generics = self.tcx.generics_of(def_id);
        for (idx, arg) in generic_args.iter().enumerate() {
            let Some(ty) = arg.as_type() else {
                continue;
            };
            if !has_fn_mut_closure(self.tcx.mk_args(&[arg])) {
                continue;
            }
            if matches!(ty.kind(), mir_ty::TyKind::Closure(..))
                && !callee_bounded.contains(&generics.param_at(idx, self.tcx).def_id)
            {
                tracing::info!(
                    ?ty,
                    "FnMut instance analyzed again: closure not at an FnMut-bounded parameter"
                );
                return false;
            }
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
        let mut pending = self.fn_mut_reuse.fn_mut_instance_obligations.borrow_mut();
        for (laws, pre) in obligations {
            pending.laws.extend(laws);
            pending.pre.extend(pre);
        }
        true
    }

    /// Pushes the obligations of [`Analyzer::reuse_fn_mut_generic`]: the precondition clauses
    /// always, the `hist_inv!` law clauses when some analysis assumed the laws of a closure type
    /// parameter's relation. That is coarser than tracking which instance reaches which
    /// relation, and only adds checks.
    pub fn emit_fn_mut_instance_obligations(&mut self) {
        let mut pending = self.fn_mut_reuse.fn_mut_instance_obligations.borrow_mut();
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
        for def in defs {
            for param in fn_mut_bounded_params(self.tcx, def.to_def_id()) {
                let name = crate::refine::stable_def_id_symbol(self.tcx, param, "q_hist_inv");
                if with_laws.contains(name.as_str()) {
                    specified.insert(param);
                }
            }
        }
        drop(system);
        *self.fn_mut_reuse.hist_inv_specified_params.borrow_mut() = specified;
    }

    /// Whether `def_id` has an `FnMut`-bounded type parameter and each of them is one whose
    /// `hist_inv!` relation the specifications use. Only such a def's instances at concrete
    /// closures may use its generic analysis ([`Analyzer::reuse_fn_mut_generic`]).
    fn is_hist_inv_specified(&self, def_id: DefId) -> bool {
        let params = fn_mut_bounded_params(self.tcx, def_id);
        let specified = self.fn_mut_reuse.hist_inv_specified_params.borrow();
        !params.is_empty() && params.iter().all(|param| specified.contains(param))
    }

    /// Whether the generic def `def_id` is verified per instance (D34): it has an `FnMut`-bounded
    /// type parameter and its contract does not relate the closure's states by `hist_inv!`.
    /// Its body is checked against its contract at each of its instances in rustc's mono item set
    /// ([`Analyzer::check_body_at_instance`]), and not over its type parameters; a call uses its
    /// contract.
    pub fn is_checked_per_instance(&self, def_id: DefId) -> bool {
        matches!(self.defs.get(&def_id), Some(DefTy::Generic(_)))
            && !fn_mut_bounded_params(self.tcx, def_id).is_empty()
            && !self.is_hist_inv_specified(def_id)
    }

    /// Records that a specification states `post!` of a state of the `FnMut`-bounded type
    /// parameter `param` held as a value. That call ends in a final state the call drops, whose
    /// resolution is known at a concrete closure only: the generic analysis does not establish
    /// it, so an instance at a closure is analyzed again rather than using the contract as
    /// instantiated, which states it.
    pub fn record_once_post_param(&self, param: DefId) {
        self.fn_mut_reuse
            .once_post_params
            .borrow_mut()
            .insert(param);
    }
}
