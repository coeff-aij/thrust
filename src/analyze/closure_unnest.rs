//! `unnest!(f, g)` between two states of a closure: Creusot's `FnMutExt::hist_inv`, called
//! `unnest` in earlier Creusot versions.
//!
//! As in Creusot (`creusot-std/src/std/ops.rs` and `closure_hist_inv` in
//! `creusot/src/backend/closures.rs`), a closure type parameter's relation is opaque and obeys
//! the laws `hist_inv_refl`, `hist_inv_trans` and `postcondition_mut_hist_inv`, stated here as
//! premises of the clauses that use it; a concrete closure's relation is defined from its
//! captures, and nothing is assumed of it.

use rustc_middle::ty as mir_ty;

use crate::chc;
use crate::rty;

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
        panic!("unnest! at a type that is not a closure: {closure_ty:?}");
    };
    match args.as_closure().kind() {
        mir_ty::ClosureKind::Fn => return from.equal_to(to).into(),
        mir_ty::ClosureKind::FnMut => {}
        mir_ty::ClosureKind::FnOnce => panic!("unnest! is defined for Fn and FnMut closures"),
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

/// The laws of the relation `pred` of a closure type parameter whose contract is `contract`.
pub fn laws(
    system: &mut chc::System,
    pred: &chc::ForallPred,
    contract: &rty::FunctionType,
) -> Vec<chc::Formula<chc::TermVarIdx>> {
    let sort = pred.params()[0].clone();
    let var = |v| chc::Term::UserQuantifiedVar(sort.clone(), v);
    let related = |from, to| -> chc::Formula<chc::TermVarIdx> {
        chc::Atom::new(pred.clone().into(), vec![from, to]).into()
    };

    let fresh = |system: &mut chc::System, name: &str| {
        system.new_named_user_quantified_var(format!("{name} in a law of {pred}"))
    };
    let f = fresh(system, "unnest_f");
    let refl = chc::Formula::forall(vec![(f, sort.clone())], related(var(f), var(f)));
    let [f, g, h] = ["unnest_f", "unnest_g", "unnest_h"].map(|n| fresh(system, n));
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
                let v = fresh(system, &format!("unnest_p{}", idx.index()));
                (v, param.ty.to_sort())
            })
            .collect();
        let args: Vec<_> = params
            .iter()
            .map(|(v, sort)| chc::Term::UserQuantifiedVar(sort.clone(), *v))
            .collect();
        let result_sort = contract.ret.ty.to_sort();
        let r = fresh(system, "unnest_r");
        let result = chc::Term::UserQuantifiedVar(result_sort.clone(), r);
        params.push((r, result_sort));
        let post = contract.postcondition_formula(&args, result);
        let states = related(args[0].clone().mut_current(), args[0].clone().mut_final());
        laws.push(chc::Formula::forall(params, post.implies(states)));
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
/// where a generic analysis uses `unnest!`. `None` when the precondition names an unknown,
/// which such a clause cannot state in Horn form; the instance is then analyzed again.
pub fn instance_obligations<'tcx>(
    tcx: mir_ty::TyCtxt<'tcx>,
    closure_ty: mir_ty::Ty<'tcx>,
    contract: &rty::FunctionType,
) -> Option<(Vec<chc::Clause>, Vec<chc::Clause>)> {
    let receiver_sort = contract.params[rty::FunctionParamIdx::from_usize(0)]
        .ty
        .to_sort();
    let upvars_sort = receiver_sort.clone().deref();
    let related = |from: chc::Term<chc::TermVarIdx>, to: chc::Term<chc::TermVarIdx>| {
        concrete_definition(tcx, closure_ty, &upvars_sort, from, to)
    };
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
        "unnest! reflexivity",
    );
    law_clauses.extend(obligation(
        vec![s(), s(), s()],
        &|v| {
            let premise =
                related(v[0].clone(), v[1].clone()).and(related(v[1].clone(), v[2].clone()));
            (premise, related(v[0].clone(), v[2].clone()))
        },
        "unnest! transitivity",
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
        "unnest! implied by each call's postcondition",
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
