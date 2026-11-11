//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300

// std's `Vec::extend` for a general iterator with its dispatch (the rust-src of nightly-2025-09-08,
// the toolchain this repository pins): `Extend::extend` of `Vec` (`library/alloc/src/vec/mod.rs`)
// calls `into_iter` and `SpecExtend::spec_extend` (`library/alloc/src/vec/spec_extend.rs`), whose
// `default` impl for every `Iterator` runs `Vec::extend_desugared`, here as in extend_desugared.rs.
// Differences from std: the three functions take the vector as a parameter instead of `self`, and
// the vector has no allocator parameter. `SpecExtend` bounds its parameters by `Model` and
// `IteratorSpec`, which its contract needs; its impl and `extend` also bound the models by
// `PartialEq`, as `#[thrust_macros::context]` bounds `extend_desugared`, which has ghost code.
// Only the general impl of `SpecExtend<T, I>` for `Vec<T>` is here. std specializes it for a
// `TrustedLen` iterator (`extend_trusted`, which runs `for_each`), for which std.rs has no spec
// trait, and for `vec::IntoIter<T>`, which copies the remaining slice with unsafe pointer code. So
// `extend` is verified with the general path at every iterator, also at those std sends down
// another one, such as the `vec::IntoIter<u32>` of `extend_index`. The contract of `extend` is
// Creusot's (`examples/iterators/08_collect_extend.rs`, 3620de437) from the iterator `into_iter`
// gives, as std.rs states `Vec::extend`'s without the `fold_completed` end it allows for the
// `TrustedLen` path; `spec_extend`'s is `extend_desugared`'s.
// Annotation code beside the invariant: the contracts of `extend` and `spec_extend`, the ghosts
// `old_vec`, `old_iter` and `produced`, the ghost `x`, the item before it moves into the vector,
// and a call of the lemma `produces_refl` before the loop.
#![feature(specialization)]
#![allow(incomplete_features)]

use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

#[thrust_macros::context]
#[thrust_macros::requires(forall(|it: <I::IntoIter as Model>::Ty| I::into_iter_is(iter, it) ==> <I::IntoIter as IteratorSpec>::inv(it)))]
#[thrust_macros::ensures(exists(|it: <I::IntoIter as Model>::Ty, prod: Seq<<T as Model>::Ty>, done: <I::IntoIter as Model>::Ty, fin: <I::IntoIter as Model>::Ty|
    I::into_iter_is(iter, it) && <I::IntoIter as IteratorSpec>::produces(it, prod, done)
        && <I::IntoIter as IteratorSpec>::completed(Mut::new(done, fin)) && !vec == (*vec).concat(prod)))]
fn extend<T: Model, I: IntoIteratorSpec<Item = T>>(vec: &mut Vec<T>, iter: I)
where
    I::IntoIter: IteratorSpec,
    <T as Model>::Ty: PartialEq,
    <I::IntoIter as Model>::Ty: PartialEq,
{
    <Vec<T> as SpecExtend<T, I::IntoIter>>::spec_extend(vec, iter.into_iter())
}

#[thrust_macros::context]
trait SpecExtend<T: Model, I: IteratorSpec<Item = T>> {
    #[thrust_macros::requires(I::inv(iter))]
    #[thrust_macros::ensures(exists(|prod: Seq<<T as Model>::Ty>, done: <I as Model>::Ty, fin: <I as Model>::Ty|
        I::completed(Mut::new(done, fin)) && I::produces(iter, prod, done) && !vec == (*vec).concat(prod)))]
    fn spec_extend(vec: &mut Vec<T>, iter: I);
}

#[thrust_macros::context]
impl<T: Model, I: IteratorSpec<Item = T>> SpecExtend<T, I> for Vec<T>
where
    <T as Model>::Ty: PartialEq,
    <I as Model>::Ty: PartialEq,
{
    default fn spec_extend(vec: &mut Vec<T>, iter: I) {
        extend_desugared(vec, iter)
    }
}

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
    extend(&mut v1, v2);
    thrust_macros::proof_assert!(|v1: Vec<u32>, old1: Ghost<Seq<<u32 as Model>::Ty>>, old2: Ghost<Seq<<u32 as Model>::Ty>>| v1 == old1.concat(old2));
}

fn main() {}
