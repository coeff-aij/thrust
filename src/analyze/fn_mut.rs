//! Reusing the generic analysis of a def at an instance whose type arguments are `FnMut`
//! closures, and the obligations that reuse records.

use std::collections::HashSet;

use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::analyze::{closure_hist_inv, Analyzer};
use crate::chc;
use crate::rty;

/// See [`Analyzer::reuse_fn_mut_generic`].
#[derive(Default)]
pub(super) struct FnMutInstanceObligations {
    laws: Vec<chc::Clause>,
    pre: Vec<chc::Clause>,
    /// The defs an instance has used the contract of as instantiated.
    reused: HashSet<DefId>,
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
    /// closure among them, can use its contract as instantiated rather than analyzing the body
    /// again. The generic analysis stands for the instance once the closures obey what it
    /// assumed of their type parameters; those obligations are recorded here. It requires:
    ///
    /// - the def, if `FnMut`-bounded, to be hist_inv-specified ([`Analyzer::is_hist_inv_specified`]);
    /// - each type argument that is an `FnMut` closure to sit at one of its `FnMut`-bounded
    ///   parameters;
    /// - each type argument that nests an `FnMut` closure (`Map<Range, F>` given to `collect`) to
    ///   nest it in local ADTs only, and every `FnMut`-bounded def reachable through them
    ///   ([`Analyzer::fn_mut_defs_reached_through`]) to be hist_inv-specified. Those defs then have
    ///   their own generic analysis emitted, so no def verified per instance is reached only
    ///   through this instance;
    /// - no unknown reachable from the contract, and a known contract for each closure.
    pub(super) fn reuse_fn_mut_generic(
        &mut self,
        def_id: DefId,
        expected: &rty::RefinedType,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        caller_def_id: DefId,
    ) -> bool {
        let callee_bounded = fn_mut_bounded_params(self.tcx, def_id);
        if !callee_bounded.is_empty() && !self.is_hist_inv_specified(def_id) {
            return false;
        }
        let generics = self.tcx.generics_of(def_id);
        let mut reached = Vec::new();
        for (idx, arg) in generic_args.iter().enumerate() {
            let Some(ty) = arg.as_type() else {
                continue;
            };
            if !has_fn_mut_closure(self.tcx.mk_args(&[arg])) {
                continue;
            }
            if matches!(ty.kind(), mir_ty::TyKind::Closure(..)) {
                if !callee_bounded.contains(&generics.param_at(idx, self.tcx).def_id) {
                    tracing::info!(
                        ?ty,
                        "FnMut instance analyzed again: closure not at an FnMut-bounded parameter"
                    );
                    return false;
                }
                continue;
            }
            let Some(defs) = self.fn_mut_defs_reached_through(ty) else {
                tracing::info!(
                    ?ty,
                    "FnMut instance analyzed again: closure nested in a type other than a local ADT"
                );
                return false;
            };
            if let Some(def) = defs.iter().find(|def| !self.is_hist_inv_specified(**def)) {
                tracing::info!(
                    ?ty,
                    ?def,
                    "FnMut instance analyzed again: a reachable FnMut-bounded def is verified per instance"
                );
                return false;
            }
            reached.extend(defs);
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
        let mut pending = self.fn_mut_instance_obligations.borrow_mut();
        if !callee_bounded.is_empty() {
            pending.reused.insert(def_id);
        }
        pending.reused.extend(reached);
        for (laws, pre) in obligations {
            pending.laws.extend(laws);
            pending.pre.extend(pre);
        }
        true
    }

    /// The local `FnMut`-bounded defs an `FnMut` closure nested in `ty` can reach as the value of
    /// one of their type parameters: the items (and the closures in them) of the local impls
    /// that name an ADT on the path from `ty` to the closure ([`Analyzer::enclosing_impl`]).
    /// `None` if the path passes through
    /// anything but a local ADT, whose impls are not all in view here.
    ///
    /// A generic body receives the closure only inside such an ADT, so it reaches the closure's
    /// type only through the ADT's impls; any other call it makes at the closure's type is made
    /// at its own type parameters and is analyzed within its own generic analysis.
    fn fn_mut_defs_reached_through(&self, ty: mir_ty::Ty<'tcx>) -> Option<Vec<DefId>> {
        let mut adts = Vec::new();
        if !self.collect_adts_to_fn_mut_closures(ty, &mut adts) {
            return None;
        }
        let names_adt = |ty: mir_ty::Ty<'tcx>| {
            ty.walk().any(|arg| {
                arg.as_type().is_some_and(|ty| {
                    matches!(ty.kind(), mir_ty::TyKind::Adt(adt, _) if adts.contains(&adt.did()))
                })
            })
        };
        let defs = self
            .fn_mut_bounded_defs
            .borrow()
            .iter()
            .copied()
            .filter(|def| {
                let Some(impl_did) = self.enclosing_impl(*def) else {
                    return false;
                };
                let self_ty = self.tcx.type_of(impl_did).instantiate_identity();
                let trait_args_name_adt = self
                    .tcx
                    .impl_trait_ref(impl_did)
                    .is_some_and(|tr| tr.instantiate_identity().args.types().any(names_adt));
                names_adt(self_ty) || trait_args_name_adt
            })
            .collect();
        Some(defs)
    }

    /// Collects the ADTs on the paths from `ty` to the `FnMut` closures in it; false if such a
    /// path passes through a type other than a local ADT.
    fn collect_adts_to_fn_mut_closures(&self, ty: mir_ty::Ty<'tcx>, adts: &mut Vec<DefId>) -> bool {
        if !has_fn_mut_closure(self.tcx.mk_args(&[ty.into()])) {
            return true;
        }
        match ty.kind() {
            mir_ty::TyKind::Closure(..) => true,
            mir_ty::TyKind::Adt(adt, args) if adt.did().is_local() => {
                adts.push(adt.did());
                args.types()
                    .all(|ty| self.collect_adts_to_fn_mut_closures(ty, adts))
            }
            _ => false,
        }
    }

    /// The impl whose type parameters `def_id` shares: that of an associated fn, or of the fn a
    /// closure is in. A fn item nested in a body has generics of its own and no such impl; it is
    /// called only from that body, at the body's type parameters.
    fn enclosing_impl(&self, def_id: DefId) -> Option<DefId> {
        let mut cursor = def_id;
        while let Some(parent) = self.tcx.generics_of(cursor).parent {
            if matches!(
                self.tcx.def_kind(parent),
                rustc_hir::def::DefKind::Impl { .. }
            ) {
                return Some(parent);
            }
            cursor = parent;
        }
        None
    }

    /// Pushes the obligations of [`Analyzer::reuse_fn_mut_generic`]: the precondition clauses
    /// always, the `hist_inv!` law clauses when some analysis assumed the laws of a closure type
    /// parameter's relation. That is coarser than tracking which instance reaches which
    /// relation, and only adds checks.
    pub fn emit_fn_mut_instance_obligations(&mut self) {
        let mut pending = self.fn_mut_instance_obligations.borrow_mut();
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
        let mut fn_mut_bounded_defs = Vec::new();
        for def in defs {
            let params = fn_mut_bounded_params(self.tcx, def.to_def_id());
            if self.tcx.def_kind(def).is_fn_like() && !params.is_empty() {
                fn_mut_bounded_defs.push(def.to_def_id());
            }
            for param in params {
                let name = crate::refine::stable_def_id_symbol(self.tcx, param, "q_hist_inv");
                if with_laws.contains(name.as_str()) {
                    specified.insert(param);
                }
            }
        }
        drop(system);
        *self.hist_inv_specified_params.borrow_mut() = specified;
        *self.fn_mut_bounded_defs.borrow_mut() = fn_mut_bounded_defs;
    }

    /// Whether `def_id` has an `FnMut`-bounded type parameter and each of them is one whose
    /// `hist_inv!` relation the specifications use. Only such a def's instances at concrete
    /// closures may use its generic analysis ([`Analyzer::reuse_fn_mut_generic`]); any other
    /// `FnMut`-bounded def is verified per instance (D34).
    pub fn is_hist_inv_specified(&self, def_id: DefId) -> bool {
        let params = fn_mut_bounded_params(self.tcx, def_id);
        let specified = self.hist_inv_specified_params.borrow();
        !params.is_empty() && params.iter().all(|param| specified.contains(param))
    }

    /// Whether an instance has used the contract of `local_def_id` as instantiated, so its
    /// generic analysis stands for that instance and must be emitted.
    pub fn has_reused_instance(&self, local_def_id: LocalDefId) -> bool {
        self.fn_mut_instance_obligations
            .borrow()
            .reused
            .contains(&local_def_id.to_def_id())
    }
}
