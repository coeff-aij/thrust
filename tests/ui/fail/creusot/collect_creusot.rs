//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Fail twin: the client's `proof_assert!` is `v[i] == i + 1`, not `v[i] == i`.
// Creusot's `collect` and `collect_example` (`examples/iterators/08_collect_extend.rs`,
// 3620de437) over the shared `Iterator` of `auxiliary/common.rs`, the specification the other
// cases use, where `collect_for.rs` is over std.rs's `IteratorSpec`. Creusot's `for x in iter`
// loop is the `while let Some(x) = it.next()` it desugars to, and its invariant
// `res@.ext_eq(*produced)` is `I::produces(iter, res, it)`, the items produced so far being the
// vector. The parameter is `it`, since the invariant's `iter` names the loop's iterator.
// `I::invariant(it)` is required where Creusot's type invariant holds by typing. Creusot's ensures
// also has `resolve(^done)`, which is not stated here: Thrust has no `resolve` predicate (fork
// issue #156), and the client does not use it.
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, FnParam, Model};

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
pub use common::Iterator;

#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(it))]
#[thrust_macros::ensures(exists(|done: <I as Model>::Ty| exists(|fin: <I as Model>::Ty|
    I::produces(it, result, done) && I::completed(Mut::new(done, fin)))))]
pub fn collect<I: Iterator>(it: I) -> Vec<I::Item>
where
    I::Item: Model,
{
    let mut iter = it;
    I::produces_refl(&iter);
    let mut res = Vec::new();
    while let Some(x) = iter.next() {
        thrust_macros::invariant!(|iter: I, res: Vec<I::Item>, it: FnParam<I>|
            I::invariant(iter) && I::produces(it.at_entry(), res, iter));
        res.push(x);
    }
    res
}

#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(it))]
#[thrust_macros::requires(forall(|prod: Seq<<u32 as Model>::Ty>, fin: <I as Model>::Ty|
    I::produces(it, prod, fin) ==> forall(|i: Int| 0 <= i && i < prod.len() ==> prod[i] == i)))]
pub fn collect_example<I: Iterator<Item = u32>>(it: I) {
    let v: Vec<u32> = collect(it);
    thrust_macros::proof_assert!(|v: Vec<u32>| forall(|i: Int| 0 <= i && i < v.len() ==> v[i] == i + 1));
}
