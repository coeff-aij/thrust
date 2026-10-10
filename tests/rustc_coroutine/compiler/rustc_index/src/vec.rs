use std::fmt;
use crate::thrust_models;
use std::borrow::{Borrow, BorrowMut};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::vec;

use thrust_models::forall;

use crate::rustc_index::{Idx, IndexSlice, SliceIter};
use crate::{IntoIteratorSpec, IteratorSpec};
use crate::case_study::USize;

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexVec<I: Idx, T> {
    pub raw: Vec<T>,
    pub(crate) _marker: PhantomData<fn(&I)>,
}

impl<I: Idx, T: fmt::Debug> fmt::Debug for IndexVec<I, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.raw, fmt)
    }
}

#[thrust_macros::context]
impl<I: Idx, T> IndexVec<I, T> {
    #[inline]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.len() == 0)]
    pub const fn new() -> Self {
        IndexVec::from_raw(Vec::new())
    }

    #[inline]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == raw)]
    pub const fn from_raw(raw: Vec<T>) -> Self {
        IndexVec {
            raw,
            _marker: PhantomData,
        }
    }

    // A written contract, so that the roots that do not select this module trust it rather than
    // analyse it: the bit-set root's specification of `vec![elem; n]` at the word type would be
    // applied to it at `T` (src/rty/subtyping.rs panics with "inconsistent types").
    #[inline]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.len() == (*universe).len()
        && forall(|k: USize| !(0 <= k && k < result.len()) || result[k] == elem))]
    pub fn from_elem<S>(elem: T, universe: &IndexSlice<I, S>) -> Self
    where
        T: Clone,
    {
        IndexVec::from_raw(vec![elem; universe.len()])
    }

    #[inline]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.len() == n)]
    #[thrust_macros::ensures(forall(|k: USize| !(0 <= k && k < n) || result[k] == elem))]
    pub fn from_elem_n(elem: T, n: usize) -> Self
    where
        T: Clone,
    {
        IndexVec::from_raw(vec![elem; n])
    }

    #[inline]
    pub fn as_slice(&self) -> &IndexSlice<I, T> {
        IndexSlice::from_raw(&self.raw)
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut IndexSlice<I, T> {
        IndexSlice::from_raw_mut(&mut self.raw)
    }

    // Rewrite (rewrites.md S8): `len`, `is_empty` and `next_index` of `IndexSlice`, restated on
    // `IndexVec` with contracts over the vector's sequence.
    #[inline]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == (*self).len())]
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    #[inline]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures((result == true) == ((*self).len() == 0))]
    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    #[inline]
    #[thrust_macros::requires(<I as Idx>::can_new((*self).len()))]
    #[thrust_macros::ensures(<I as Idx>::index_is(result, (*self).len()))]
    pub fn next_index(&self) -> I {
        I::new(self.raw.len())
    }

    #[inline]
    #[thrust_macros::requires(<I as Idx>::can_new((*self).len()))]
    #[thrust_macros::ensures(!self == (*self).push(d))]
    #[thrust_macros::ensures(<I as Idx>::index_is(result, (*self).len()))]
    pub fn push(&mut self, d: T) -> I {
        let idx = self.next_index();
        self.raw.push(d);
        idx
    }
}

impl<I: Idx, T> Deref for IndexVec<I, T> {
    type Target = IndexSlice<I, T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<I: Idx, T> DerefMut for IndexVec<I, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<I: Idx, T> Borrow<IndexSlice<I, T>> for IndexVec<I, T> {
    fn borrow(&self) -> &IndexSlice<I, T> {
        self
    }
}

impl<I: Idx, T> BorrowMut<IndexSlice<I, T>> for IndexVec<I, T> {
    fn borrow_mut(&mut self) -> &mut IndexSlice<I, T> {
        self
    }
}

impl<I: Idx, T> Extend<T> for IndexVec<I, T> {
    #[inline]
    // Not analysed and not callable: `layout()` calls `extend_from` (rewrites.md R8) instead.
    #[thrust::ignored]
    fn extend<J: IntoIterator<Item = T>>(&mut self, iter: J) {
        self.raw.extend(iter);
    }
}

impl<I: Idx, T> FromIterator<T> for IndexVec<I, T> {
    #[inline]
    // Not analysed and not callable: its only caller, the `collect` in `univariant_biased`, is
    // trusted.
    #[thrust::ignored]
    fn from_iter<J>(iter: J) -> Self
    where
        J: IntoIterator<Item = T>,
    {
        IndexVec::from_raw(Vec::from_iter(iter))
    }
}

impl<I: Idx, T> IntoIterator for IndexVec<I, T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;

    #[inline]
    fn into_iter(self) -> vec::IntoIter<T> {
        self.raw.into_iter()
    }
}

// Rewrite (rewrites.md R4): `SliceIter` for `slice::Iter`, as `IndexSlice::iter` returns.
impl<'a, I: Idx, T: thrust_models::Model<Ty: PartialEq>> IntoIterator for &'a IndexVec<I, T> {
    type Item = &'a T;
    type IntoIter = SliceIter<'a, T>;

    #[inline]
    fn into_iter(self) -> SliceIter<'a, T> {
        self.iter()
    }
}

impl<'a, I: Idx, T: thrust_models::Model<Ty: PartialEq>> IntoIterator for &'a mut IndexVec<I, T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> std::slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

// The iterators the three `into_iter`s start, as std.rs's `IntoIteratorSpec` of `Vec` says.
#[thrust_macros::context]
impl<I: Idx + thrust_models::Model<Ty: PartialEq>, T: thrust_models::Model> IntoIteratorSpec for IndexVec<I, T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: vec::IntoIter<T>) -> bool {
        it.0 == self && it.1 == 0 && <vec::IntoIter<T> as IteratorSpec>::inv(it)
    }
}

#[thrust_macros::context]
impl<'a, I: Idx + thrust_models::Model<Ty: PartialEq>, T: thrust_models::Model + 'a> IntoIteratorSpec for &'a IndexVec<I, T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: SliceIter<'a, T>) -> bool {
        *it.0 == *self && it.1 == 0 && <SliceIter<'a, T> as IteratorSpec>::inv(it)
    }
}

#[thrust_macros::context]
impl<'a, I: Idx + thrust_models::Model<Ty: PartialEq>, T: thrust_models::Model + 'a> IntoIteratorSpec for &'a mut IndexVec<I, T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: std::slice::IterMut<'a, T>) -> bool {
        it.0 == *self && it.1 == !self && it.2 == 0 && (!self).len() == (*self).len()
    }
}

impl<I: Idx, T, const N: usize> From<[T; N]> for IndexVec<I, T> {
    #[inline]
    fn from(array: [T; N]) -> Self {
        IndexVec::from_raw(array.into())
    }
}
