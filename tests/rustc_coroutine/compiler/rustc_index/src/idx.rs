use crate::thrust_models;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::slice::SliceIndex;

use thrust_models::{exists, forall};

use crate::IteratorSpec;
use crate::case_study::USize;

#[thrust_macros::context]
pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    #[thrust_macros::predicate]
    fn can_new(idx: USize) -> bool;

    #[thrust_macros::predicate]
    fn index_is(self, i: USize) -> bool;

    #[thrust_macros::requires(Self::can_new(idx))]
    #[thrust_macros::ensures(Self::index_is(result, idx))]
    fn new(idx: usize) -> Self;

    #[thrust_macros::ensures(Self::index_is(self, result))]
    fn index(self) -> usize;

    #[inline]
    #[thrust_macros::requires(
        thrust_models::forall(|i: USize|
            Self::index_is(*self, i) ==> Self::can_new(i + amount)
        )
    )]
    fn increment_by(&mut self, amount: usize) {
        *self = self.plus(amount);
    }

    #[inline]
    #[must_use = "Use `increment_by` if you wanted to update the index in-place"]
    #[thrust_macros::requires(
        thrust_models::forall(|i: USize|
            Self::index_is(self, i) ==> Self::can_new(i + amount)
        )
    )]
    #[thrust_macros::ensures(forall(|i: USize, a: USize|
        Self::index_is(self, i) && a == amount ==> Self::index_is(result, i + a)))]
    fn plus(self, amount: usize) -> Self {
        Self::new(self.index() + amount)
    }

    // `index` is a function, so an element has exactly one index. Creusot gets this for free from
    // a logic function; `index_is` is a predicate, so the two halves are laws.
    #[thrust_macros::law]
    #[thrust_macros::requires(Self::index_is(*a, i) && Self::index_is(*a, j))]
    #[thrust_macros::ensures(i == j)]
    #[thrust::trusted]
    fn index_is_unique(a: &Self, i: usize, j: usize) {}

    #[thrust_macros::law]
    #[thrust_macros::ensures(exists(|i: USize| Self::index_is(*a, i)))]
    #[thrust::trusted]
    fn index_is_total(a: &Self) {}

    // Two elements with the same index are equal, which `layout()`'s `v == index` needs.
    #[thrust_macros::law]
    #[thrust_macros::requires(Self::index_is(*a, i) && Self::index_is(*b, i))]
    #[thrust_macros::ensures(*a == *b)]
    #[thrust::trusted]
    fn index_is_injective(a: &Self, b: &Self, i: usize) {}
}

#[thrust_macros::context]
impl Idx for usize {
    #[thrust_macros::predicate]
    fn can_new(idx: USize) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn index_is(self, i: USize) -> bool {
        i == self
    }

    #[inline]
    fn new(idx: usize) -> Self {
        idx
    }
    #[inline]
    fn index(self) -> usize {
        self
    }
}

#[thrust_macros::context]
impl Idx for u32 {
    #[thrust_macros::predicate]
    fn can_new(idx: USize) -> bool {
        // idx <= u32::MAX
        idx <= 4294967295usize
    }

    #[thrust_macros::predicate]
    fn index_is(self, i: USize) -> bool {
        i == self
    }

    #[inline]
    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }
    #[inline]
    fn index(self) -> usize {
        self as usize
    }
}

/// Own iterator standing in for `(start..end).map(I::new)`: yields
/// `I::new(start)`, `I::new(start + 1)`, ..., `I::new(end - 1)`.
// `Clone` commented out: deriving it on this generic struct panics Thrust with `unbound var $0`
// (src/chc/clause_builder.rs:113) while analysing `<IdxRange<I> as Clone>::clone`, on the inner
// `<PhantomData<I> as Clone>::clone` call.
// #[derive(Clone)]
pub struct IdxRange<I: Idx> {
    pub(crate) start: usize,
    pub(crate) end: usize,
    marker: PhantomData<I>,
}

#[thrust_macros::context]
impl<I: Idx> IdxRange<I> {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.start == start && result.end == end)]
    pub(crate) fn new(start: usize, end: usize) -> IdxRange<I> {
        IdxRange {
            start,
            end,
            marker: PhantomData,
        }
    }
}

// `IdxRange`'s model is the struct itself, so `(*self).start` keeps its Rust type `usize` in a
// formula; the `s == (*self).start` guards under `forall` pass it to `Idx`'s predicates.
#[thrust_macros::context]
impl<I: Idx + thrust_models::Model> Iterator for IdxRange<I>
where
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = I;

    #[thrust_macros::requires(
        forall(|s: USize| s == (*self).start && s < (*self).end ==> <I as Idx>::can_new(s))
    )]
    #[thrust_macros::ensures(
        forall(|s: USize| s == (*self).start && s < (*self).end
            ==> exists(|x: <I as thrust_models::Model>::Ty|
                    result == Some(x) && <I as Idx>::index_is(x, s))
                && s + 1 == (!self).start
                && (!self).end == (*self).end)
    )]
    #[thrust_macros::ensures(
        !((*self).start < (*self).end)
            ==> result == None && (!self).start == (*self).start && (!self).end == (*self).end
    )]
    fn next(&mut self) -> Option<I> {
        if self.start < self.end {
            let n = self.start;
            self.start += 1;
            Some(I::new(n))
        } else {
            None
        }
    }
}

// The positions left are buildable; `produces` and `completed` restate `next`'s contract.
#[thrust_macros::context]
impl<I: Idx + thrust_models::Model> IteratorSpec for IdxRange<I>
where
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        forall(|a: USize, b: USize, s: USize|
            !(a == self.start && b == self.end && a <= s && s < b) || <I as Idx>::can_new(s))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<I>, o: Self) -> bool {
        self.end == o.end
            && forall(|a: USize, b: USize, e: USize|
                !(a == self.start && b == o.start && e == o.end)
                    || (a <= b
                        && (visited.len() == 0 || b <= e)
                        && visited.len() == b - a
                        && forall(|i: USize| !(0 <= i && i < visited.len()) || <I as Idx>::index_is(visited[i], a + i))))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).start >= (*self).end && (!self).start == (*self).start && (!self).end == (*self).end
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::context]
pub trait IntoSliceIdx<I, T: ?Sized + thrust_models::Model<Ty: PartialEq>> {
    type Output: SliceIndex<T>;

    /// `out` is the slice position `self` selects.
    #[thrust_macros::predicate]
    fn into_is(self, out: Self::Output) -> bool;

    fn into_slice_idx(self) -> Self::Output;
}

#[thrust_macros::context]
impl<I: Idx, T: thrust_models::Model<Ty: PartialEq>> IntoSliceIdx<I, [T]> for I {
    type Output = usize;

    #[thrust_macros::predicate]
    fn into_is(self, out: usize) -> bool {
        <I as Idx>::index_is(self, out)
    }

    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        self.index()
    }
}
