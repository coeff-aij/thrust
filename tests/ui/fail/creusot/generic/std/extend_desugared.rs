//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300

// The fail twin of extend_desugared.rs: the loop discards each item instead of pushing it.
// std's `Vec::extend_desugared` (`library/alloc/src/vec/mod.rs` of the rust-src of
// nightly-2025-09-08, the toolchain this repository pins), the loop of `extend` and `collect` for a
// general iterator, as a free function over std.rs's `IteratorSpec`. Differences from std: the body
// of the loop is `push`, for std's capacity check, `reserve` by the iterator's `size_hint`, unsafe
// write and `set_len`, which together are what `push` does; and a ghost sequence `produced` records
// the items taken, which Creusot gives a `for` loop and `while let` has none. The contract is
// Creusot's `extend` (`examples/iterators/08_collect_extend.rs`, 3620de437).
// The parameters are moved into `v` and `it` before the loop, so that its `invariant!` can name
// their values at entry through `FnParam` binders named `vec` and `iterator`; a written invariant
// states everything the rest of the function needs. Annotation code beside the invariant: the
// ghosts `old_vec`, `old_iter` and `produced`, the ghost `x`, the item before it moves into the
// vector, and a call of the lemma `produces_refl` before the loop.
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(iterator))]
#[thrust_macros::ensures(exists(|done: <I as Model>::Ty| exists(|fin: <I as Model>::Ty| exists(|prod: Seq<<T as Model>::Ty>|
    I::completed(Mut::new(done, fin)) && I::produces(iterator, prod, done) && !vec == (*vec).concat(prod)))))]
fn extend_desugared<T: Model, I: IteratorSpec<Item = T>>(vec: &mut Vec<T>, iterator: I) {
    let v = vec;
    let mut it = iterator;
    let old_vec = thrust_macros::ghost!(|v: &mut Vec<T>| -> Seq<<T as Model>::Ty> { *v });
    let old_iter = thrust_macros::ghost!(|it: I| -> I { it });
    let mut produced = thrust_macros::ghost!(|| -> Seq<<T as Model>::Ty> { Seq::empty() });
    I::produces_refl(&it);
    while let Some(element) = it.next() {
        thrust_macros::invariant!(|it: I, v: &mut Vec<T>, old_vec: Ghost<Seq<<T as Model>::Ty>>, old_iter: Ghost<I>, produced: Ghost<Seq<<T as Model>::Ty>>, vec: thrust_models::FnParam<&mut Vec<T>>, iterator: thrust_models::FnParam<I>|
            I::inv(it)
                && I::produces(old_iter, produced, it)
                && *v == old_vec.concat(produced)
                && !v == !vec.at_entry()
                && old_vec == *vec.at_entry()
                && old_iter == iterator.at_entry());
        let x = thrust_macros::ghost!(|element: T| -> T { element });
        let _dropped = element;
        produced = thrust_macros::ghost!(|produced: Ghost<Seq<<T as Model>::Ty>>, x: Ghost<T>| -> Seq<<T as Model>::Ty> { produced.push(x) });
    }
}

#[thrust_macros::context]
#[thrust::callable]
fn extend_index(mut v1: Vec<u32>, v2: Vec<u32>) {
    let old1 = thrust_macros::ghost!(|v1: Vec<u32>| -> Seq<<u32 as Model>::Ty> { v1 });
    let old2 = thrust_macros::ghost!(|v2: Vec<u32>| -> Seq<<u32 as Model>::Ty> { v2 });
    extend_desugared(&mut v1, v2.into_iter());
    thrust_macros::proof_assert!(|v1: Vec<u32>, old1: Ghost<Seq<<u32 as Model>::Ty>>, old2: Ghost<Seq<<u32 as Model>::Ty>>| v1 == old1.concat(old2));
}

fn main() {}
