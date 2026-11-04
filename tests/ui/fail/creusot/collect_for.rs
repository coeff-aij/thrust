//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The fail twin of collect_for.rs: the assertion claims each element is one more than its index.
// Creusot's `collect` and `collect_example` (`examples/iterators/08_collect_extend.rs`): a `for`
// loop over an iterator implementing std.rs's `IteratorSpec`, whose invariant states that the
// vector is the sequence `produced`. The parameter is `it`, since the invariant's `iter` names the
// loop's iterator; `I::inv(it)` is required where Creusot's type invariant holds by typing.
// Creusot's ensures also has `resolve(^done)`, which is not stated here; the client does not use it.
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(exists(|done: <I as Model>::Ty| exists(|fin: <I as Model>::Ty|
    I::produces(it, result, done) && I::completed(Mut::new(done, fin)))))]
fn collect<I: IteratorSpec>(it: I) -> Vec<I::Item>
where
    I::Item: Model,
{
    let mut res = Vec::new();
    for x in it {
        thrust_macros::invariant!(|iter: I, iter_old: Ghost<I>, produced: Ghost<Seq<<I::Item as Model>::Ty>>, res: Vec<I::Item>, it: thrust_models::FnParam<I>|
            iter_old == it.at_entry() && res == produced);
        res.push(x);
    }
    res
}

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::requires(forall(|prod: Seq<<u32 as Model>::Ty>, fin: <I as Model>::Ty|
    I::produces(it, prod, fin) ==> forall(|i: Int| 0 <= i && i < prod.len() ==> prod[i] == i)))]
fn collect_example<I: IteratorSpec<Item = u32>>(it: I) {
    let v: Vec<u32> = collect(it);
    thrust_macros::proof_assert!(|v: Vec<u32>| forall(|i: Int| 0 <= i && i < v.len() ==> v[i] == i + 1));
}

fn main() {}
