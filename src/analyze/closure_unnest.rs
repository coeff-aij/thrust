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
    pred: &chc::ForallPred,
    contract: &rty::FunctionType,
) -> Vec<chc::Formula<chc::TermVarIdx>> {
    let sort = pred.params()[0].clone();
    let var = |name: &str| chc::Term::FormulaQuantifiedVar(sort.clone(), name.to_owned());
    let related = |from, to| -> chc::Formula<chc::TermVarIdx> {
        chc::Atom::new(pred.clone().into(), vec![from, to]).into()
    };
    let vars = |names: &[&str]| -> Vec<(String, chc::Sort)> {
        names
            .iter()
            .map(|name| (name.to_string(), sort.clone()))
            .collect()
    };

    let refl = chc::Formula::forall(
        vars(&["unnest_f"]),
        related(var("unnest_f"), var("unnest_f")),
    );
    let trans = chc::Formula::forall(
        vars(&["unnest_f", "unnest_g", "unnest_h"]),
        related(var("unnest_f"), var("unnest_g"))
            .and(related(var("unnest_g"), var("unnest_h")))
            .implies(related(var("unnest_f"), var("unnest_h"))),
    );
    let mut laws = vec![refl, trans];

    let receiver = &contract.params[rty::FunctionParamIdx::from_usize(0)].ty;
    let receiver_kind = receiver.as_pointer().map(|ty| ty.kind);
    if receiver_kind == Some(rty::PointerKind::Ref(rty::RefKind::Mut)) {
        let mut params: Vec<(String, chc::Sort)> = contract
            .params
            .iter_enumerated()
            .map(|(idx, param)| (format!("unnest_p{}", idx.index()), param.ty.to_sort()))
            .collect();
        let args: Vec<_> = params
            .iter()
            .map(|(name, sort)| chc::Term::FormulaQuantifiedVar(sort.clone(), name.clone()))
            .collect();
        let result_sort = contract.ret.ty.to_sort();
        let result = chc::Term::FormulaQuantifiedVar(result_sort.clone(), "unnest_r".to_owned());
        params.push(("unnest_r".to_owned(), result_sort));
        let post = contract.postcondition_formula(&args, result);
        let states = related(args[0].clone().mut_current(), args[0].clone().mut_final());
        laws.push(chc::Formula::forall(params, post.implies(states)));
    }
    for law in &mut laws {
        law.simplify();
    }
    laws
}
