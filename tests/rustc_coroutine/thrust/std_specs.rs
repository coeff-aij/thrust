//! Specifications of std functions the case study calls that std.rs does not specify.
//!
//! The exact `wrapping_add` and `wrapping_sub` specs below are full functional specs, valid at every
//! call site, and belong in std.rs; they stay here until they move there.

use crate::thrust_models;
use thrust_models::model::BitVec;

// The two methods `Niche::available` calls. Each is exact over 128-bit bit-vectors.
#[thrust::extern_spec_fn]
#[thrust_macros::ensures(result == (BitVec::<128, false>::from_int(x) + BitVec::from_int(y)).to_int())]
fn _extern_spec_u128_wrapping_add(x: u128, y: u128) -> u128 {
    u128::wrapping_add(x, y)
}

#[thrust::extern_spec_fn]
#[thrust_macros::ensures(result == (BitVec::<128, false>::from_int(x) - BitVec::from_int(y)).to_int())]
fn _extern_spec_u128_wrapping_sub(x: u128, y: u128) -> u128 {
    u128::wrapping_sub(x, y)
}

// `Hash64::wrapping_add` and the layout seeds, exact over 64-bit bit-vectors.
#[thrust::extern_spec_fn]
#[thrust_macros::ensures(result == (BitVec::<64, false>::from_int(x) + BitVec::from_int(y)).to_int())]
fn _extern_spec_u64_wrapping_add(x: u64, y: u64) -> u64 {
    u64::wrapping_add(x, y)
}

// `fold` over a slice iterator calls the closure on each item from the cursor on. Its result is
// not stated: the case study only needs that it does not panic.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(thrust_models::forall(|c: thrust_models::model::Closure<F>,
    b: <B as thrust_models::Model>::Ty, x: <&'a T as thrust_models::Model>::Ty|
    thrust_macros::pre!(c(b, x))))]
#[thrust_macros::ensures(true)]
fn _extern_spec_slice_iter_fold<'a, T, B, F>(it: core::slice::Iter<'a, T>, init: B, f: F) -> B
where
    T: thrust_models::Model + 'a,
    B: thrust_models::Model,
    F: FnMut(B, &'a T) -> B,
{
    <core::slice::Iter<'a, T> as Iterator>::fold(it, init, f)
}

// `max` calls `next` until it returns `None`. Its result is not stated: the case study only needs
// that it does not panic.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(I::inv(it))]
#[thrust_macros::ensures(true)]
fn _extern_spec_iterator_max<I>(it: I) -> Option<I::Item>
where
    I: crate::IteratorSpec,
    I::Item: thrust_models::Model + Ord,
{
    <I as Iterator>::max(it)
}

// The `Vec == array` of `univariant_biased`'s `assert_eq!` (from branch univariant-spec 03bffcea):
// a `Vec` and an array are both modelled as a sequence, and the element type's `==` is its model
// equality, as std.rs's generic `eq` assumes.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*x == *y))]
fn _extern_spec_vec_partialeq_array_eq<T, const N: usize>(x: &Vec<T>, y: &[T; N]) -> bool
where
    T: thrust_models::Model + PartialEq,
{
    <Vec<T> as PartialEq<[T; N]>>::eq(x, y)
}
