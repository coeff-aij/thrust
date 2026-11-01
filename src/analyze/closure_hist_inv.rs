//! `hist_inv!(f, g)` between two states of a closure: Creusot's `FnMutExt::hist_inv`, called
//! `unnest` in earlier Creusot versions.
//!
//! As in Creusot (`creusot-std/src/std/ops.rs` and `closure_hist_inv` in
//! `creusot/src/backend/closures.rs`), a closure type parameter's relation is opaque and obeys
//! the laws `hist_inv_refl`, `hist_inv_trans` and `postcondition_mut_hist_inv`, stated here as
//! premises of the clauses that use it; a concrete closure's relation is defined from its
//! captures, together with the relation its `closure!` specification writes in a `hist_inv`
//! clause, which the closure is checked to obey ([`explicit_laws`]). Without such a clause,
//! where Creusot says nothing of a capture taken by value, the relation of those captures is an
//! unknown inferred under the same laws ([`by_value_relation_laws`]).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use rustc_middle::ty as mir_ty;
use rustc_span::def_id::DefId;

use crate::analyze::{self, Analyzer};
use crate::chc;
use crate::rty;

/// The relations `hist_inv!` stands for at concrete closures, made on first use.
#[derive(Clone, Default)]
pub(super) struct HistInvRelations<'tcx> {
    /// The closure types, generic arguments included, with the sort of their upvars, whose
    /// `hist_inv` clause has had its laws pushed; see [`explicit_laws`].
    explicit_hist_inv_laws: Rc<RefCell<HashSet<(mir_ty::Ty<'tcx>, chc::Sort)>>>,
    /// The unknown relating the by-value captures of an `FnMut` closure whose specification has
    /// no `hist_inv` clause, one per closure type and upvars sort; see
    /// [`Analyzer::closure_hist_inv_definition`].
    by_value_hist_invs: Rc<RefCell<HashMap<(mir_ty::Ty<'tcx>, chc::Sort), chc::PredVarId>>>,
}

/// The positions and sorts of the captures of the `FnMut` closure `closure_ty` taken by value,
/// which the relation [`concrete_definition`] derives says nothing of. Empty for an `Fn` closure.
pub fn by_value_captures<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    closure_ty: mir_ty::Ty<'tcx>,
    upvars_sort: &chc::Sort,
) -> Vec<(usize, chc::Sort)> {
    let mir_ty::TyKind::Closure(def_id, args) = closure_ty.kind() else {
        return Vec::new();
    };
    if args.as_closure().kind() != mir_ty::ClosureKind::FnMut {
        return Vec::new();
    }
    let chc::Sort::Tuple(upvar_sorts) = upvars_sort else {
        return Vec::new();
    };
    let captures = tcx.closure_captures(def_id.expect_local());
    captures
        .iter()
        .zip(upvar_sorts)
        .enumerate()
        .filter(|(_, (capture, sort))| {
            !sort.is_singleton()
                && matches!(
                    capture.info.capture_kind,
                    mir_ty::UpvarCapture::ByValue | mir_ty::UpvarCapture::ByUse
                )
        })
        .map(|(idx, (_, sort))| (idx, sort.clone()))
        .collect()
}

/// `relation` applied to the captures at `positions` of the states `from` and `to`.
pub fn by_value_related<V: chc::Var>(
    relation: chc::PredVarId,
    positions: &[usize],
    from: chc::Term<V>,
    to: chc::Term<V>,
) -> chc::Formula<V> {
    let args = positions
        .iter()
        .map(|idx| from.clone().tuple_proj(*idx))
        .chain(positions.iter().map(|idx| to.clone().tuple_proj(*idx)))
        .collect();
    chc::Atom::new(relation.into(), args).into()
}

/// The clauses that make `relation`, over the by-value captures of sorts `sorts` at two states,
/// reflexive and transitive. That each call's postcondition implies it is checked against the
/// closure's body, since the postcondition includes it.
pub fn by_value_relation_laws(relation: chc::PredVarId, sorts: &[chc::Sort]) -> Vec<chc::Clause> {
    type States = [Vec<chc::Term<chc::TermVarIdx>>];
    let law = |states: usize, build: &dyn Fn(&States) -> Obligation, what: &str| {
        let mut builder = chc::ClauseBuilder::default();
        let vars: Vec<Vec<_>> = (0..states)
            .map(|_| {
                sorts
                    .iter()
                    .map(|sort| chc::Term::var(builder.add_var(sort.clone())))
                    .collect()
            })
            .collect();
        let (premise, conclusion) = build(&vars);
        let origin = crate::chc::debug::origin::Entry::described(format!(
            "{what} of the by-value captures' hist_inv! relation {relation:?}"
        ));
        builder.add_body(premise.into(), origin.clone());
        builder.head(conclusion.into(), origin)
    };
    let related = |from: &[chc::Term<chc::TermVarIdx>], to: &[chc::Term<chc::TermVarIdx>]| {
        chc::Formula::from(chc::Atom::new(
            relation.into(),
            from.iter().chain(to).cloned().collect(),
        ))
    };
    let mut clauses = law(
        1,
        &|v| (chc::Formula::top(), related(&v[0], &v[0])),
        "reflexivity",
    );
    clauses.extend(law(
        3,
        &|v| {
            (
                related(&v[0], &v[1]).and(related(&v[1], &v[2])),
                related(&v[0], &v[2]),
            )
        },
        "transitivity",
    ));
    clauses
}

/// The relation at a concrete closure: an `Fn` closure's state never changes, and an `FnMut`
/// closure keeps the final value of every capture borrowed by `&mut` and the value of every
/// capture borrowed by `&`. A capture taken by value says nothing, since the closure may
/// replace it.
pub fn concrete_definition<'tcx, V: chc::Var>(
    tcx: mir_ty::TyCtxt<'tcx>,
    closure_ty: mir_ty::Ty<'tcx>,
    upvars_sort: &chc::Sort,
    from: chc::Term<V>,
    to: chc::Term<V>,
) -> chc::Formula<V> {
    let mir_ty::TyKind::Closure(def_id, args) = closure_ty.kind() else {
        panic!("hist_inv! at a type that is not a closure: {closure_ty:?}");
    };
    match args.as_closure().kind() {
        mir_ty::ClosureKind::Fn => return from.equal_to(to).into(),
        mir_ty::ClosureKind::FnMut => {}
        mir_ty::ClosureKind::FnOnce => panic!("hist_inv! is defined for Fn and FnMut closures"),
    }
    let chc::Sort::Tuple(upvar_sorts) = upvars_sort else {
        panic!("closure upvars in an unexpected shape: {upvars_sort:?}");
    };
    let captures = tcx.closure_captures(def_id.expect_local());
    assert_eq!(captures.len(), upvar_sorts.len());
    let mut formula = chc::Formula::top();
    for (idx, (capture, sort)) in captures.iter().zip(upvar_sorts).enumerate() {
        if sort.is_singleton() {
            continue;
        }
        let from = from.clone().tuple_proj(idx);
        let to = to.clone().tuple_proj(idx);
        let kept = match capture.info.capture_kind {
            mir_ty::UpvarCapture::ByValue | mir_ty::UpvarCapture::ByUse => continue,
            mir_ty::UpvarCapture::ByRef(mir_ty::BorrowKind::Immutable) => to.equal_to(from),
            mir_ty::UpvarCapture::ByRef(_) => to.mut_final().equal_to(from.mut_final()),
        };
        formula = formula.and(kept.into());
    }
    formula
}

/// The clauses checking that `related`, the relation an `hist_inv` clause of `closure_ty`'s
/// specification gives over its upvars of sort `upvars_sort`, is reflexive and transitive.
/// That each call's postcondition implies it is checked against the closure's body, since the
/// postcondition includes it.
pub fn explicit_laws(
    closure_ty: mir_ty::Ty<'_>,
    upvars_sort: &chc::Sort,
    related: &dyn Fn(
        chc::Term<chc::TermVarIdx>,
        chc::Term<chc::TermVarIdx>,
    ) -> chc::Formula<chc::TermVarIdx>,
) -> Vec<chc::Clause> {
    let law =
        |states: usize, build: &dyn Fn(&[chc::Term<chc::TermVarIdx>]) -> Obligation, what: &str| {
            let mut builder = chc::ClauseBuilder::default();
            let vars: Vec<_> = (0..states)
                .map(|_| chc::Term::var(builder.add_var(upvars_sort.clone())))
                .collect();
            let (premise, conclusion) = build(&vars);
            let origin = crate::chc::debug::origin::Entry::described(format!(
                "{what} of the hist_inv clause of {closure_ty:?}"
            ));
            builder.add_body(premise.into(), origin.clone());
            builder.head(conclusion.into(), origin)
        };
    let mut clauses = law(
        1,
        &|v| (chc::Formula::top(), related(v[0].clone(), v[0].clone())),
        "reflexivity",
    );
    clauses.extend(law(
        3,
        &|v| {
            let premise =
                related(v[0].clone(), v[1].clone()).and(related(v[1].clone(), v[2].clone()));
            (premise, related(v[0].clone(), v[2].clone()))
        },
        "transitivity",
    ));
    clauses
}

/// The laws of the relation `pred` of a closure type parameter whose contract is `contract`.
pub fn laws(
    system: &mut chc::System,
    pred: &chc::ForallPred,
    contract: &rty::FunctionType,
    enum_defs: &dyn rty::EnumDefProvider,
) -> Vec<chc::Formula<chc::TermVarIdx>> {
    let sort = pred.params()[0].clone();
    let var = |v| chc::Term::UserQuantifiedVar(sort.clone(), v);
    let related = |from, to| -> chc::Formula<chc::TermVarIdx> {
        chc::Atom::new(pred.clone().into(), vec![from, to]).into()
    };

    let fresh = |system: &mut chc::System, name: &str| {
        system.new_named_user_quantified_var(format!("{name} in a law of {pred}"))
    };
    let f = fresh(system, "hist_inv_f");
    let refl = chc::Formula::forall(vec![(f, sort.clone())], related(var(f), var(f)));
    let [f, g, h] = ["hist_inv_f", "hist_inv_g", "hist_inv_h"].map(|n| fresh(system, n));
    let trans = chc::Formula::forall(
        vec![(f, sort.clone()), (g, sort.clone()), (h, sort.clone())],
        related(var(f), var(g))
            .and(related(var(g), var(h)))
            .implies(related(var(f), var(h))),
    );
    let mut laws = vec![refl, trans];

    let receiver = &contract.params[rty::FunctionParamIdx::from_usize(0)].ty;
    let receiver_kind = receiver.as_pointer().map(|ty| ty.kind);
    if receiver_kind == Some(rty::PointerKind::Ref(rty::RefKind::Mut)) {
        let mut params: Vec<(chc::UserQuantifiedVarId, chc::Sort)> = contract
            .params
            .iter_enumerated()
            .map(|(idx, param)| {
                let v = fresh(system, &format!("hist_inv_p{}", idx.index()));
                (v, param.ty.to_sort())
            })
            .collect();
        let args: Vec<_> = params
            .iter()
            .map(|(v, sort)| chc::Term::UserQuantifiedVar(sort.clone(), *v))
            .collect();
        let result_sort = contract.ret.ty.to_sort();
        let r = fresh(system, "hist_inv_r");
        let result = chc::Term::UserQuantifiedVar(result_sort.clone(), r);
        params.push((r, result_sort));
        let mut premise = contract.postcondition_formula(&args, result.clone());
        // The law's variables range over the types of the parameters and the result.
        let typed = contract
            .params
            .iter()
            .zip(&args)
            .map(|(param, arg)| (&param.ty, arg));
        for (ty, term) in typed.chain([(&contract.ret.ty, &result)]) {
            let payload = || fresh(system, "hist_inv_payload");
            if let Some((vars, range)) =
                rty::int_range_type_formula(ty, term.clone(), payload, enum_defs)
            {
                params.extend(vars);
                premise = range.and(premise);
            }
        }
        let states = related(args[0].clone().mut_current(), args[0].clone().mut_final());
        laws.push(chc::Formula::forall(params, premise.implies(states)));
    }
    for law in &mut laws {
        law.simplify();
    }
    laws
}

/// A premise and the conclusion it must imply.
type Obligation = (chc::Formula<chc::TermVarIdx>, chc::Formula<chc::TermVarIdx>);

/// What the generic analysis of an `FnMut`-bounded def assumes of its closure type parameter,
/// stated of the concrete `FnMut` closure `closure_ty` with contract `contract` as clauses to
/// check at an instance that reuses that analysis instead of analyzing the body again:
///
/// - the three laws of [`laws`], of the relation [`concrete_definition`] gives this closure;
/// - that the precondition does not read the final half of the receiver pair. The generic call
///   discharges its closure's precondition at the current state alone (`pre_upvars_sort` in
///   `refine::template`), while the closure's body is checked assuming it of the pair.
///
/// Returns the law clauses and the precondition clauses apart, since the laws are assumed only
/// where a generic analysis uses `hist_inv!`. `None` when the precondition names an unknown,
/// which such a clause cannot state in Horn form; the instance is then analyzed again.
pub fn instance_obligations(
    closure_ty: mir_ty::Ty<'_>,
    contract: &rty::FunctionType,
    related: &dyn Fn(
        chc::Term<chc::TermVarIdx>,
        chc::Term<chc::TermVarIdx>,
    ) -> chc::Formula<chc::TermVarIdx>,
) -> Option<(Vec<chc::Clause>, Vec<chc::Clause>)> {
    let receiver_sort = contract.params[rty::FunctionParamIdx::from_usize(0)]
        .ty
        .to_sort();
    let upvars_sort = receiver_sort.clone().deref();
    let obligation = |sorts: Vec<chc::Sort>,
                      build: &dyn Fn(&[chc::Term<chc::TermVarIdx>]) -> Obligation,
                      what: &str| {
        let mut builder = chc::ClauseBuilder::default();
        let vars: Vec<_> = sorts
            .into_iter()
            .map(|sort| chc::Term::var(builder.add_var(sort)))
            .collect();
        let (premise, conclusion) = build(&vars);
        let origin = crate::chc::debug::origin::Entry::described(format!(
            "{what} of {closure_ty:?}, assumed by a generic analysis"
        ));
        builder.add_body(premise.into(), origin.clone());
        builder.head(conclusion.into(), origin)
    };

    let s = || upvars_sort.clone();
    let mut law_clauses = obligation(
        vec![s()],
        &|v| (chc::Formula::top(), related(v[0].clone(), v[0].clone())),
        "hist_inv! reflexivity",
    );
    law_clauses.extend(obligation(
        vec![s(), s(), s()],
        &|v| {
            let premise =
                related(v[0].clone(), v[1].clone()).and(related(v[1].clone(), v[2].clone()));
            (premise, related(v[0].clone(), v[2].clone()))
        },
        "hist_inv! transitivity",
    ));
    let param_sorts: Vec<chc::Sort> = contract
        .params
        .iter()
        .map(|param| param.ty.to_sort())
        .collect();
    let mut post_sorts = param_sorts.clone();
    post_sorts.push(contract.ret.ty.to_sort());
    law_clauses.extend(obligation(
        post_sorts,
        &|v| {
            let (result, args) = v.split_last().unwrap();
            let post = contract.postcondition_formula(args, result.clone());
            let receiver = args[0].clone();
            (
                post,
                related(receiver.clone().mut_current(), receiver.mut_final()),
            )
        },
        "hist_inv! implied by each call's postcondition",
    ));

    // The precondition at the pair `(current, final)` against the one at `(current, current)`.
    let mut pre_sorts = param_sorts;
    pre_sorts.push(upvars_sort.clone());
    let pre = |v: &[chc::Term<chc::TermVarIdx>], final_: chc::Term<chc::TermVarIdx>| {
        let (_, params) = v.split_last().unwrap();
        let mut args = params.to_vec();
        args[0] = chc::Term::mut_(params[0].clone().mut_current(), final_);
        contract.precondition_formula(&args)
    };
    let probe_vars: Vec<_> = (0..pre_sorts.len())
        .map(|idx| chc::Term::var(chc::TermVarIdx::from_usize(idx)))
        .collect();
    let probe = pre(&probe_vars, probe_vars.last().unwrap().clone());
    if probe
        .iter_atoms()
        .any(|atom| matches!(atom.pred, chc::Pred::Var(_)))
    {
        return None;
    }
    let pre_clauses = obligation(
        pre_sorts,
        &|v| {
            let final_ = v.last().unwrap().clone();
            let current = v[0].clone().mut_current();
            (pre(v, current), pre(v, final_))
        },
        "precondition independent of the receiver's final state",
    );
    Some((law_clauses, pre_clauses))
}

impl<'tcx> Analyzer<'tcx> {
    /// The relation of `hist_inv!` at the concrete closure `closure_ty` whose upvars have the sort
    /// `upvars_sort`, between the states `from` and `to`: the one its captures give, and the one
    /// the `hist_inv` clause of its specification writes, if any.
    pub fn closure_hist_inv_definition<V: chc::Var>(
        &self,
        closure_ty: mir_ty::Ty<'tcx>,
        upvars_sort: &chc::Sort,
        from: chc::Term<V>,
        to: chc::Term<V>,
    ) -> chc::Formula<V> {
        let derived =
            concrete_definition(self.tcx, closure_ty, upvars_sort, from.clone(), to.clone());
        if let Some(explicit) =
            self.closure_explicit_hist_inv(closure_ty, upvars_sort, from.clone(), to.clone())
        {
            return derived.and(explicit);
        }
        let positions: Vec<usize> = by_value_captures(self.tcx, closure_ty, upvars_sort)
            .into_iter()
            .map(|(idx, _)| idx)
            .collect();
        if positions.is_empty() {
            return derived;
        }
        let relation = self.by_value_hist_inv(closure_ty, upvars_sort);
        derived.and(by_value_related(relation, &positions, from, to))
    }

    /// The unknown relating the by-value captures of `closure_ty`, whose specification writes
    /// no `hist_inv` clause, made with its laws on first use. Where Creusot says nothing of
    /// those captures, the relation is inferred like any other unknown: reflexive and transitive
    /// by these clauses, and implied by each call's postcondition, which includes it.
    fn by_value_hist_inv(
        &self,
        closure_ty: mir_ty::Ty<'tcx>,
        upvars_sort: &chc::Sort,
    ) -> chc::PredVarId {
        let key = (closure_ty, upvars_sort.clone());
        if let Some(relation) = self
            .hist_inv_relations
            .by_value_hist_invs
            .borrow()
            .get(&key)
        {
            return *relation;
        }
        let sorts: Vec<chc::Sort> = by_value_captures(self.tcx, closure_ty, upvars_sort)
            .into_iter()
            .map(|(_, sort)| sort)
            .collect();
        let sig = sorts.iter().chain(&sorts).cloned().collect();
        let relation = self
            .system
            .borrow_mut()
            .new_pred_var(sig, chc::DebugInfo::from_current_span());
        for clause in by_value_relation_laws(relation, &sorts) {
            self.system.borrow_mut().push_clause(clause);
        }
        // Its laws are pushed here and each call's step comes from the closure's body, so a
        // callee whose contract reaches it needs no analysis at the instance to define it.
        self.system.borrow_mut().mark_self_defined(relation);
        self.hist_inv_relations
            .by_value_hist_invs
            .borrow_mut()
            .insert(key, relation);
        relation
    }

    /// The relation the `hist_inv` clause of `closure_ty`'s specification writes, between the
    /// states `from` and `to`, with its laws pushed on first use.
    fn closure_explicit_hist_inv<V: chc::Var>(
        &self,
        closure_ty: mir_ty::Ty<'tcx>,
        upvars_sort: &chc::Sort,
        from: chc::Term<V>,
        to: chc::Term<V>,
    ) -> Option<chc::Formula<V>> {
        let mir_ty::TyKind::Closure(def_id, closure_args) = closure_ty.kind() else {
            return None;
        };
        let local_def_id = def_id.as_local()?;
        let (formula_def_id, path_args) = self
            .extract_path_and_args_with_attr(local_def_id, &analyze::annot::hist_inv_path_path())?;
        let formula_def_id = formula_def_id.expect_local();
        let generic_args = self.closure_spec_args(path_args, *def_id, closure_args);
        let owner_fn_id = self.tcx.typeck_root_def_id(*def_id);
        let formula_fn = self
            .formula_fn_with_args(formula_def_id, generic_args, owner_fn_id)
            .expect("hist_inv clause is not a formula function");
        let apply = |from: chc::Term<V>, to: chc::Term<V>| {
            let pair = chc::Term::mut_(from, to);
            formula_fn.formula().clone().subst_var(|_| pair.clone())
        };
        if self
            .hist_inv_relations
            .explicit_hist_inv_laws
            .borrow_mut()
            .insert((closure_ty, upvars_sort.clone()))
        {
            let related = |from: chc::Term<chc::TermVarIdx>, to: chc::Term<chc::TermVarIdx>| {
                let pair = chc::Term::mut_(from, to);
                formula_fn.formula().clone().subst_var(|_| pair.clone())
            };
            let laws = explicit_laws(closure_ty, upvars_sort, &related);
            for clause in laws {
                self.system.borrow_mut().push_clause(clause);
            }
        }
        Some(apply(from, to))
    }

    /// The generic arguments of a `closure!` specification's formula function at the closure
    /// arguments `closure_args`: `path_args`, the arguments its marker path is written with, over
    /// the parameters of the closure's parent and in the formula function's own order, at the
    /// closure's parent arguments. `closure_args` may be the closure's own arguments or its
    /// parent's alone, the key a deferred closure is analyzed under; `body_args` widens the latter.
    pub(super) fn closure_spec_args(
        &self,
        path_args: mir_ty::GenericArgsRef<'tcx>,
        closure_def_id: DefId,
        closure_args: mir_ty::GenericArgsRef<'tcx>,
    ) -> mir_ty::GenericArgsRef<'tcx> {
        let closure_args = analyze::body_args(self.tcx, closure_def_id, closure_args);
        mir_ty::EarlyBinder::bind(path_args)
            .instantiate(self.tcx, closure_args.as_closure().parent_args())
    }
}
