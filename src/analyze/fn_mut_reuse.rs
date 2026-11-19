//! Reusing the generic analysis of a def at an instance whose type arguments are `FnMut`
//! closures, and the obligations that reuse records.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;

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

/// Whether the body of the local fn `def_id` calls a def with an `FnMut`-bounded type parameter at
/// type arguments that hold an `FnMut` closure of its own, one whose type depends on its type
/// parameters. The closure's contract is built where the closure is, so the callee's instance and
/// the closure meet only in an analysis of `def_id` at an instance.
fn passes_own_closure_to_fn_mut_def<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    use rustc_middle::ty::TypeVisitableExt as _;

    let Some(local_def_id) = def_id.as_local() else {
        return false;
    };
    if tcx.is_closure_like(def_id) || tcx.hir_maybe_body_owned_by(local_def_id).is_none() {
        return false;
    }
    let typeck = tcx.typeck(local_def_id);
    let holds_own_closure = |(callee, args): (DefId, mir_ty::GenericArgsRef<'tcx>)| {
        !fn_mut_bounded_params(tcx, callee).is_empty()
            && args
                .types()
                .any(|ty| ty.has_param() && has_fn_mut_closure(tcx.mk_args(&[ty.into()])))
    };
    let method_call = typeck
        .type_dependent_defs()
        .items()
        .filter_map(|(local_id, res)| {
            let (_, callee) = res.as_ref().ok()?;
            let hir_id = rustc_hir::HirId {
                owner: typeck.hir_owner,
                local_id,
            };
            Some((*callee, typeck.node_args(hir_id)))
        })
        .any(holds_own_closure);
    method_call
        || typeck
            .node_types()
            .items()
            .filter_map(|(_, ty)| match ty.kind() {
                mir_ty::TyKind::FnDef(callee, args) => Some((*callee, *args)),
                _ => None,
            })
            .any(holds_own_closure)
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
    /// closure nested in a type argument, can use its contract as instantiated rather than
    /// analyzing the body again. The generic analysis stands for the instance once the closures
    /// obey what it assumed of their type parameters; those obligations are recorded here. It
    /// requires:
    ///
    /// - no type argument that is itself an `FnMut` closure: the def has no `FnMut`-bounded
    ///   parameter to take it at;
    /// - no unknown reachable from the contract, and a known contract for each closure.
    ///
    /// A def with an `FnMut`-bounded parameter never comes here
    /// ([`Analyzer::is_checked_per_instance`]).
    pub(super) fn reuse_fn_mut_generic(
        &mut self,
        expected: &rty::RefinedType,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> bool {
        for arg in generic_args.iter() {
            let Some(ty) = arg.as_type() else {
                continue;
            };
            if matches!(ty.kind(), mir_ty::TyKind::Closure(..))
                && has_fn_mut_closure(self.tcx.mk_args(&[arg]))
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

    /// Whether the generic def `def_id` is verified per instance: it has an `FnMut`-bounded type
    /// parameter. Its body is checked against its contract at each of its instances in rustc's
    /// mono item set ([`Analyzer::check_body_at_instance`]), over its type parameters only when
    /// it has none; a call uses its contract.
    pub fn is_checked_per_instance(&self, def_id: DefId) -> bool {
        matches!(self.defs.get(&def_id), Some(DefTy::Generic(_)))
            && (!fn_mut_bounded_params(self.tcx, def_id).is_empty()
                || passes_own_closure_to_fn_mut_def(self.tcx, def_id))
    }
}
