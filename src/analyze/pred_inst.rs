//! Emitting a generic item's `#[thrust_macros::predicate]` at a concrete
//! instantiation.
//!
//! A predicate written in a generic impl is read once, with the impl's type
//! parameters standing as forall sorts, and defined as one `define-fun` over
//! those sorts. A forall sort is rigid in the solver's logic — it is one fixed
//! unknown sort, not a sort variable — so that definition cannot be applied
//! anywhere but the generic clauses it was read for. A call site that
//! instantiates the impl speaks of the instance's own sorts and needs its own
//! copy: the sorts become the instance's, the trait predicates reached through a
//! type parameter become the predicates of the impl the parameter was given, and
//! the pre/postcondition of a closure parameter becomes the contract of the
//! closure it was given.
//!
//! The body is the SMT-LIB2 string the source carries, so the rewriting is
//! textual. It splits in two: the predicate substitution happens here, where
//! trait selection can say what each reference resolves to, and the sort
//! substitution is handed to the emitter, which is the first place the datatype
//! naming is settled.

use std::collections::{HashMap, HashSet};

use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

use crate::analyze;
use crate::chc::{self, ForallSortIdx};
use crate::refine;
use crate::rty;

/// Where a [`chc::ForallPred`] standing for a trait predicate came from, so that
/// an instantiation can resolve it.
#[derive(Debug, Clone, Copy)]
pub struct ForallPredOrigin<'tcx> {
    pub def_id: DefId,
    pub generic_args: mir_ty::GenericArgsRef<'tcx>,
}

/// One predicate definition waiting to be emitted at an instantiation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PendingPredInstance<'tcx> {
    pred_def_id: DefId,
    generic_args: mir_ty::GenericArgsRef<'tcx>,
    owner_fn_id: DefId,
}

impl<'tcx> analyze::Analyzer<'tcx> {
    /// Records that `pred` stands for `def_id` applied at `generic_args`, which
    /// are written in the analyzed item's own parameters.
    pub fn register_forall_pred_origin(
        &self,
        pred: chc::ForallPred,
        def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
    ) {
        self.forall_pred_origins.borrow_mut().insert(
            pred,
            ForallPredOrigin {
                def_id,
                generic_args,
            },
        );
    }

    /// The symbol a reference to `pred_def_id` at `generic_args` must use, and,
    /// when that is an instantiation of a generic item, a request to emit the
    /// matching definition.
    pub fn user_defined_pred_at_args(
        &self,
        pred_def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> chc::UserDefinedPred {
        let Some(instance) = self.pred_instance_sorts(pred_def_id, generic_args, owner_fn_id)
        else {
            return refine::user_defined_pred(self.tcx(), pred_def_id);
        };
        self.pending_pred_instances
            .borrow_mut()
            .push(PendingPredInstance {
                pred_def_id,
                generic_args,
                owner_fn_id,
            });
        refine::user_defined_pred_at_instance(self.tcx(), pred_def_id, instance)
    }

    /// The sorts that identify this instantiation, or `None` when there is
    /// nothing to instantiate: the predicate is not one this crate defines, the
    /// declaring item takes no type parameters, or the arguments are the generic
    /// template's own.
    fn pred_instance_sorts(
        &self,
        pred_def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<Vec<chc::Sort>> {
        use mir_ty::TypeVisitableExt as _;

        if pred_def_id.as_local().is_none() || generic_args.has_param() {
            return None;
        }
        let type_builder = self.type_builder(self.def_ids(), owner_fn_id);
        let sorts: Vec<_> = generic_args
            .types()
            .map(|ty| type_builder.build(ty).to_sort())
            .collect();
        if sorts.is_empty() {
            return None;
        }
        Some(sorts)
    }

    /// Emits every predicate definition requested during analysis, and every one
    /// those definitions request in turn.
    pub fn emit_pending_pred_instances(&mut self) {
        let mut seen = HashSet::new();
        loop {
            let pending: Vec<_> = std::mem::take(&mut *self.pending_pred_instances.borrow_mut());
            if pending.is_empty() {
                break;
            }
            for request in pending {
                if !seen.insert(request) {
                    continue;
                }
                self.emit_pred_instance(request);
            }
        }
    }

    fn emit_pred_instance(&mut self, request: PendingPredInstance<'tcx>) {
        let PendingPredInstance {
            pred_def_id,
            generic_args,
            owner_fn_id,
        } = request;
        let Some(instance) = self.pred_instance_sorts(pred_def_id, generic_args, owner_fn_id)
        else {
            return;
        };
        let symbol = refine::user_defined_pred_at_instance(self.tcx(), pred_def_id, instance);
        if self.system.borrow().is_pred_defined(&symbol) {
            return;
        }

        let local_def_id = pred_def_id.expect_local();
        let (sig, body) = {
            let mut analyzer = self.local_def_analyzer(local_def_id);
            analyzer.owner_fn_id(owner_fn_id).generic_args(generic_args);
            analyzer.predicate_definition()
        };

        let sort_subst = self.forall_sort_substitution(pred_def_id, generic_args, owner_fn_id);
        let body = self.substitute_forall_preds(&body, &sort_subst, generic_args, owner_fn_id);

        self.system.borrow_mut().push_pred_define_at_instance(
            symbol,
            sig,
            body,
            sort_subst.into_iter().collect(),
        );
    }

    /// Maps each forall sort the declaring item issued for one of its type
    /// parameters (or for a projection out of one) to the sort the
    /// instantiation gives it.
    fn forall_sort_substitution(
        &self,
        pred_def_id: DefId,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> HashMap<ForallSortIdx, chc::Sort> {
        let tcx = self.tcx();
        let type_builder = self.type_builder(self.def_ids(), owner_fn_id);
        let args: Vec<_> = generic_args.types().collect();

        // The items whose parameters `pred_def_id` can see: its own and every
        // ancestor's.
        let mut owners = vec![pred_def_id];
        let mut cursor = pred_def_id;
        while let Some(parent) = tcx.opt_parent(cursor) {
            owners.push(parent);
            cursor = parent;
        }

        let entries: Vec<_> = self
            .type_params
            .borrow()
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        let mut subst = HashMap::new();
        for (type_param, idx) in &entries {
            let analyze::TypeParam::GenericType {
                param_def_id,
                local_idx,
            } = type_param
            else {
                continue;
            };
            if !owners.contains(&tcx.parent(*param_def_id)) {
                continue;
            }
            let Some(arg) = args.get(*local_idx as usize) else {
                continue;
            };
            subst.insert(*idx, type_builder.build(*arg).to_sort());
        }
        // A projection's arguments are type parameters of the same item, so the
        // instantiation resolves it by normalizing it at the arguments above.
        for (type_param, idx) in &entries {
            let analyze::TypeParam::AssocType(def_id, alias_args) = type_param else {
                continue;
            };
            let mapped: Option<Vec<_>> = alias_args
                .iter()
                .map(|arg| match arg {
                    rty::Type::Param(p) => args.get(usize::from(p.type_param_index())).copied(),
                    _ => None,
                })
                .collect();
            let Some(mapped) = mapped else { continue };
            if mapped.is_empty() {
                continue;
            }
            let projection = mir_ty::Ty::new_projection(
                tcx,
                *def_id,
                tcx.mk_args_from_iter(mapped.into_iter().map(mir_ty::GenericArg::from)),
            );
            let Ok(normalized) = tcx.try_normalize_erasing_regions(
                mir_ty::TypingEnv::fully_monomorphized(),
                projection,
            ) else {
                continue;
            };
            if normalized == projection {
                continue;
            }
            subst.insert(*idx, type_builder.build(normalized).to_sort());
        }
        subst
    }

    /// Rewrites every [`chc::ForallPred`] reference in `body` to the predicate
    /// the instantiation resolves it to.
    fn substitute_forall_preds(
        &mut self,
        body: &str,
        sort_subst: &HashMap<ForallSortIdx, chc::Sort>,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> String {
        use crate::chc::format_context::format_forall_pred_name;

        let referenced: Vec<_> = self
            .system
            .borrow()
            .forall_preds()
            .map(|p| (p.clone(), format_forall_pred_name(p)))
            .filter(|(_, name)| body.contains(name.as_str()))
            .collect();

        let mut out = body.to_string();
        for (pred, name) in referenced {
            let target = self
                .resolve_forall_pred(&pred, sort_subst, generic_args, owner_fn_id)
                .unwrap_or_else(|| {
                    panic!(
                        "predicate body refers to {name}, which this instantiation \
                         gives no definition"
                    )
                });
            out = out.replace(name.as_str(), &target);
        }
        out
    }

    fn resolve_forall_pred(
        &mut self,
        pred: &chc::ForallPred,
        sort_subst: &HashMap<ForallSortIdx, chc::Sort>,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<String> {
        let origin = self.forall_pred_origins.borrow().get(pred).copied();
        let Some(ForallPredOrigin {
            def_id,
            generic_args: pred_args,
        }) = origin
        else {
            return self.define_closure_contract(pred, sort_subst, generic_args, owner_fn_id);
        };
        let pred_args = mir_ty::EarlyBinder::bind(pred_args).instantiate(self.tcx(), generic_args);
        let instance = mir_ty::Instance::try_resolve(
            self.tcx(),
            mir_ty::TypingEnv::post_analysis(self.tcx(), owner_fn_id),
            def_id,
            pred_args,
        )
        .ok()??;
        Some(
            self.user_defined_pred_at_args(instance.def_id(), instance.args, owner_fn_id)
                .to_string(),
        )
    }

    /// Defines the pre/postcondition a closure type parameter stands for as the
    /// contract of the closure the instantiation gives it, and names it.
    fn define_closure_contract(
        &mut self,
        pred: &chc::ForallPred,
        sort_subst: &HashMap<ForallSortIdx, chc::Sort>,
        generic_args: mir_ty::GenericArgsRef<'tcx>,
        owner_fn_id: DefId,
    ) -> Option<String> {
        let post = if pred.inner().starts_with("q_pre_") {
            false
        } else if pred.inner().starts_with("q_post_") {
            true
        } else {
            return None;
        };
        let [chc::Sort::Forall(param_sort)] = pred.type_parameters() else {
            return None;
        };
        let local_idx = self.type_param_local_idx(*param_sort)?;
        let closure_ty = generic_args.types().nth(local_idx)?;
        let mir_ty::TyKind::Closure(closure_def_id, closure_args) = closure_ty.kind() else {
            return None;
        };
        let fn_ty = self.known_function_ty_with_args(
            *closure_def_id,
            self.tcx().mk_args(closure_args.as_closure().parent_args()),
            owner_fn_id,
        )?;

        // The definition takes the forall predicate's parameters read at this
        // instantiation, so it keeps the argument order and the `FnMut` upvars
        // pairing of whatever the body already passes.
        let subst = |idx| sort_subst.get(&idx).cloned();
        let params: Vec<chc::Sort> = pred
            .params()
            .iter()
            .map(|s| s.subst_forall(&subst))
            .collect();
        let symbol = chc::UserDefinedPred::at_instance(pred.inner().to_string(), params.clone());
        let name = symbol.to_string();
        if self.system.borrow().is_pred_defined(&symbol) {
            return Some(name);
        }

        let vars: rustc_index::IndexVec<chc::TermVarIdx, chc::Sort> =
            params.iter().cloned().collect();
        let terms: Vec<chc::Term<chc::TermVarIdx>> = vars.indices().map(chc::Term::var).collect();
        let upvars = closure_upvars_term(terms.first()?.clone(), params.first()?, &fn_ty);
        let formula = if post {
            let (result, args) = terms.get(1..)?.split_last()?;
            let call_args: Vec<_> = std::iter::once(upvars)
                .chain(args.iter().cloned())
                .collect();
            fn_ty.postcondition_formula(&call_args, result.clone())
        } else {
            let call_args: Vec<_> = std::iter::once(upvars)
                .chain(terms.get(1..)?.iter().cloned())
                .collect();
            fn_ty.precondition_formula(&call_args)
        };

        let sig: chc::UserDefinedPredSig = vars
            .iter_enumerated()
            .map(|(v, s)| (v.to_string(), s.clone()))
            .collect();
        self.system.borrow_mut().push_pred_define_formula(
            symbol,
            sig,
            chc::Clause::for_pred_body(vars, formula),
        );
        Some(name)
    }

    fn type_param_local_idx(&self, sort_idx: ForallSortIdx) -> Option<usize> {
        self.type_params
            .borrow()
            .iter()
            .find_map(|(type_param, idx)| match type_param {
                analyze::TypeParam::GenericType { local_idx, .. } if *idx == sort_idx => {
                    Some(*local_idx as usize)
                }
                _ => None,
            })
    }
}

/// The upvars argument a closure contract takes, given the sort the predicate
/// declares for it: an `FnMut` precondition is declared over the current half of
/// the prophecy pair, while the contract itself reads plain upvars.
fn closure_upvars_term(
    term: chc::Term<chc::TermVarIdx>,
    declared: &chc::Sort,
    fn_ty: &rty::FunctionType,
) -> chc::Term<chc::TermVarIdx> {
    let contract_sort = fn_ty.params[rty::FunctionParamIdx::from_usize(0)]
        .ty
        .to_sort();
    if declared == &contract_sort {
        term
    } else {
        term.mut_current()
    }
}
