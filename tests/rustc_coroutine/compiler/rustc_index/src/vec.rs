use crate::thrust_models;
use std::borrow::{Borrow, BorrowMut};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::vec;

use thrust_models::forall;

use crate::rustc_index::{Idx, IndexSlice};
use crate::case_study::USize;

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexVec<I: Idx, T> {
    pub raw: Vec<T>,
    pub(crate) _marker: PhantomData<fn(&I)>,
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

    #[inline]
    // Not analysed and not callable: its only caller, `univariant_biased`, is trusted, and the
    // bit-set root's specification of `vec![elem; n]` at the word type would be applied to it
    // at `T` (src/rty/subtyping.rs panics with "inconsistent types").
    #[thrust::ignored]
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
    // trusted, and std.rs's iterator specifications are not used (rewrites.md R9).
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
    // Not analysed and not callable: nothing calls it, and std.rs's iterator specifications are
    // not used (rewrites.md R9).
    #[thrust::ignored]
    fn into_iter(self) -> vec::IntoIter<T> {
        self.raw.into_iter()
    }
}

impl<I: Idx, T, const N: usize> From<[T; N]> for IndexVec<I, T> {
    #[inline]
    fn from(array: [T; N]) -> Self {
        IndexVec::from_raw(array.into())
    }
}
