//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Creusot's `extend` and `extend_index` (`examples/iterators/08_collect_extend.rs`): a `for` loop
// over an iterator implementing std.rs's `IteratorSpec`, whose invariant states that the vector is
// its entry value followed by `produced`. The parameter is `it`, since the invariant's `iter` names
// the loop's iterator; `I::inv(it)` is required where Creusot's type invariant holds by typing. The
// vector reference is moved into `v` so that the invariant can name both its current value and the
// parameter's entry value, which Creusot keeps in `snapshot! { vec }`. Creusot's ensures also has
// `resolve(^done)`, which is not stated here; `extend_index` does not use it.
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, FnParam, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(exists(|done: <I as Model>::Ty| exists(|fin: <I as Model>::Ty| exists(|prod: Seq<<T as Model>::Ty>|
    I::completed(Mut::new(done, fin)) && I::produces(it, prod, done) && !vec == (*vec).concat(prod)))))]
fn extend<T: Model, I: IteratorSpec<Item = T>>(vec: &mut Vec<T>, it: I) {
    let v = vec;
    for x in it {
        thrust_macros::invariant!(|iter: I, iter_old: Ghost<I>, produced: Ghost<Seq<<T as Model>::Ty>>, v: &mut Vec<T>, it: FnParam<I>, vec: FnParam<&mut Vec<T>>|
            iter_old == it.at_entry() && !v == !vec.at_entry() && *v == (*vec.at_entry()).concat(produced));
        v.push(x);
    }
}

#[thrust_macros::context]
#[thrust::callable]
fn extend_index(mut v1: Vec<u32>, v2: Vec<u32>) {
    let old1 = thrust_macros::ghost!(|v1: Vec<u32>| -> Seq<<u32 as Model>::Ty> { v1 });
    let old2 = thrust_macros::ghost!(|v2: Vec<u32>| -> Seq<<u32 as Model>::Ty> { v2 });
    extend(&mut v1, v2.into_iter());
    thrust_macros::proof_assert!(|v1: Vec<u32>, old1: Ghost<Seq<<u32 as Model>::Ty>>, old2: Ghost<Seq<<u32 as Model>::Ty>>| v1 == old1.concat(old2));
}

fn main() {}
