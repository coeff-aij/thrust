//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_SPLIT_GOALS=1

// std's `Vec::extend_desugared` (alloc/src/vec/mod.rs, toolchain 1.94.1), the loop of `extend`
// and `collect` for a general iterator, with std's loop as a free function over std.rs's
// `IteratorSpec`. Deviation: the body of the loop is `push`, for std's capacity check, `reserve`
// by the iterator's `size_hint`, unsafe write and `set_len`, which together are what `push` does.
// The contract is Creusot's `extend` (`examples/iterators/08_collect_extend.rs`, 3620de437). The
// ghost `produced` is the items taken so far, which Creusot gives a `for` loop; `while let` has
// none, so it is written here, and kept in the inferred variant as ghost code.
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(iterator))]
#[thrust_macros::ensures(exists(|done: <I as Model>::Ty| exists(|fin: <I as Model>::Ty| exists(|prod: Seq<<T as Model>::Ty>|
    I::completed(Mut::new(done, fin)) && I::produces(iterator, prod, done) && !vec == (*vec).concat(prod)))))]
fn extend_desugared<T: Model, I: IteratorSpec<Item = T>>(vec: &mut Vec<T>, mut iterator: I) {
    let old_vec = thrust_macros::ghost!(|vec: &mut Vec<T>| -> Seq<<T as Model>::Ty> { *vec });
    let old_iter = thrust_macros::ghost!(|iterator: I| -> I { iterator });
    let mut produced = thrust_macros::ghost!(|| -> Seq<<T as Model>::Ty> { Seq::empty() });
    I::produces_refl(&iterator);
    while let Some(element) = iterator.next() {
        thrust_macros::partial_invariant!(|iterator: I, vec: &mut Vec<T>, old_vec: Ghost<Seq<<T as Model>::Ty>>, old_iter: Ghost<I>, produced: Ghost<Seq<<T as Model>::Ty>>|
            I::inv(iterator) && I::produces(old_iter, produced, iterator) && *vec == old_vec.concat(produced));
        let x = thrust_macros::ghost!(|element: T| -> T { element });
        vec.push(element);
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
