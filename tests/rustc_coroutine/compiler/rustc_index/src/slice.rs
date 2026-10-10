use crate::thrust_models;
use std::marker::PhantomData;
use std::slice::SliceIndex;

use thrust_models::forall;
use thrust_models::model::Seq;

use crate::rustc_index::{Idx, IdxRange, IndexVec, IntoSliceIdx};
use crate::case_study::USize;
use crate::case_study::iter::{IterMut, Iterator};

// `PartialEq, Eq` commented out: the derived `eq` compares the `PhantomData`
// field, whose model is the unit sort, and Thrust panics with
// `unbound var $0` -- the same reason bit_set.rs drops them from `DenseBitSet`.
#[derive(/* PartialEq, Eq, */ Hash)]
#[repr(transparent)]
pub struct IndexSlice<I: Idx, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: [T],
}

/// Own iterator standing in for `slice::Iter<'a, T>` (whose raw pointer
/// fields have no model in Thrust): yields `&raw[0]`, ..., `&raw[len - 1]`.
pub struct SliceIter<'a, T> {
    pub(crate) raw: &'a [T],
    pub(crate) pos: usize,
}

#[thrust_macros::context]
impl<'a, T: thrust_models::Model> Iterator for SliceIter<'a, T>
where
    T::Ty: PartialEq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.pos < self.raw.len() {
            let item = &self.raw[self.pos];
            self.pos += 1;
            Some(item)
        } else {
            None
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        0 <= self.1 && self.1 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && forall(|i: USize| !(0 <= i && i < visited.len()) || visited[i] == &self.0[self.1 + i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 >= (*self).0.len() && *self == !self
    }
}

/// Own iterator standing in for
/// `raw.iter().enumerate().map(|(n, t)| (I::new(n), t))`: yields
/// `(I::new(0), &raw[0])`, ..., `(I::new(len - 1), &raw[len - 1])`.
pub struct IterEnumerated<'a, I: Idx, T> {
    raw: &'a [T],
    pos: usize,
    marker: PhantomData<I>,
}

#[thrust_macros::context]
impl<'a, I: Idx + thrust_models::Model, T: thrust_models::Model> Iterator for IterEnumerated<'a, I, T>
where
    I::Ty: PartialEq,
    T::Ty: PartialEq,
{
    type Item = (I, &'a T);

    fn next(&mut self) -> Option<(I, &'a T)> {
        if self.pos < self.raw.len() {
            let n = self.pos;
            self.pos += 1;
            Some((I::new(n), &self.raw[n]))
        } else {
            None
        }
    }

    // `next` builds `I::new(pos)`, so the invariant carries `can_new` of the positions left.
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        0 <= self.1 && self.1 <= self.0.len()
            && forall(|k: USize| !(self.1 <= k && k < self.0.len()) || <I as Idx>::can_new(k))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && forall(|i: USize| !(0 <= i && i < visited.len())
                || (<I as Idx>::index_is(visited[i].0, self.1 + i) && visited[i].1 == &self.0[self.1 + i]))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 >= (*self).0.len() && *self == !self
    }
}

#[thrust_macros::context]
impl<I: Idx, T> IndexSlice<I, T> {
    // The reinterpretation through a raw pointer has no model; it is the
    // identity on the sequence, which is what the contract says.
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(*result == *raw)]
    pub const fn from_raw(raw: &[T]) -> &Self {
        let ptr: *const [T] = raw;

        unsafe { &*(ptr as *const Self) }
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(*result == *raw && !result == !raw)]
    pub fn from_raw_mut(raw: &mut [T]) -> &mut Self {
        let ptr: *mut [T] = raw;

        unsafe { &mut *(ptr as *mut Self) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.raw.len()
    }

    #[inline]
    #[thrust_macros::requires(<I as Idx>::can_new((*self).len()))]
    #[thrust_macros::ensures(<I as Idx>::index_is(result, (*self).len()))]
    pub fn next_index(&self) -> I {
        I::new(self.len())
    }

    #[inline]
    #[thrust_macros::ensures(*result.0 == *self && result.1 == 0)]
    pub fn iter(&self) -> SliceIter<'_, T> {
        SliceIter {
            raw: &self.raw,
            pos: 0,
        }
    }

    #[inline]
    #[thrust_macros::requires(<I as Idx>::can_new((*self).len()))]
    #[thrust_macros::ensures(*result.0 == *self && result.1 == 0)]
    pub fn iter_enumerated(&self) -> IterEnumerated<'_, I, T> {
        let _ = I::new(self.len());
        IterEnumerated {
            raw: &self.raw,
            pos: 0,
            marker: PhantomData,
        }
    }

    #[inline]
    #[thrust_macros::requires(<I as Idx>::can_new((*self).len()))]
    pub fn indices(&self) -> IdxRange<I> {
        let _ = I::new(self.len());
        IdxRange::new(0, self.len())
    }
}

#[thrust_macros::context]
impl<I: Idx, T: thrust_models::Model> IndexSlice<I, T>
where
    T::Ty: PartialEq,
{
    // Rewrite (rewrites.md R9): the case study's `IterMut` for `slice::IterMut`.
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.0 == *self && result.1 == !self && result.2 == 0 && (!self).len() == (*self).len())]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut { inner: self.raw.iter_mut() }
    }
}

#[thrust_macros::context]
impl<I: Idx + thrust_models::Model<Ty: PartialEq>, J: Idx + thrust_models::Model<Ty: PartialEq>> IndexSlice<I, J> {
    // `debug_assert_eq!` calls dropped (debug assertions are off; rewrites.md S6). The body
    // panics when an element is not below the length (`inverse[i2]`) or an index up to the length
    // cannot be built (`iter_enumerated`).
    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::requires(forall(|k: USize| !(0 <= k && k <= (*self).len()) || <I as Idx>::can_new(k)))]
    #[thrust_macros::requires(forall(|k: USize, i: USize|
        !(0 <= k && k < (*self).len() && <J as Idx>::index_is((*self)[k], i)) || i < (*self).len()))]
    // The inverse has the same length, and each entry is a position of `self` (or the `new(0)` it
    // starts from), so below the length.
    #[thrust_macros::ensures(result.len() == (*self).len())]
    #[thrust_macros::ensures(forall(|k: USize, i: USize|
        !(0 <= k && k < result.len() && <I as Idx>::index_is(result[k], i)) || i < result.len()))]
    pub fn invert_bijective_mapping(&self) -> IndexVec<J, I> {
        let mut inverse = IndexVec::from_elem_n(Idx::new(0), self.len());
        let mut entries = self.iter_enumerated();
        while let Some((i1, &i2)) = entries.next() {
            inverse[i2] = i1;
        }
        inverse
    }
}

impl<I: Idx, T: thrust_models::Model<Ty: PartialEq>, R: IntoSliceIdx<I, [T]>> std::ops::Index<R> for IndexSlice<I, T> {
    type Output = <R::Output as SliceIndex<[T]>>::Output;

    #[thrust::trusted]
    #[inline]
    fn index(&self, index: R) -> &Self::Output {
        &self.raw[index.into_slice_idx()]
    }
}

impl<I: Idx, T: thrust_models::Model<Ty: PartialEq>, R: IntoSliceIdx<I, [T]>> std::ops::IndexMut<R> for IndexSlice<I, T> {
    #[thrust::trusted]
    #[inline]
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        &mut self.raw[index.into_slice_idx()]
    }
}

// `Index`/`IndexMut` are foreign traits, so the contract is an extern spec (the impl methods
// are `trusted`). `IntoSliceIdx` has one impl, `I: Idx` into `usize`, through `Idx::index_is`.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(forall(|i: USize| <R as IntoSliceIdx<I, [T]>>::into_is(index, i) ==> i < (*slf).len()))]
#[thrust_macros::ensures(forall(|i: USize| <R as IntoSliceIdx<I, [T]>>::into_is(index, i) ==> *result == (*slf)[i]))]
fn _extern_spec_index_slice_index<I: Idx + thrust_models::Model<Ty: PartialEq>, T: thrust_models::Model, R: IntoSliceIdx<I, [T], Output = usize> + thrust_models::Model>(slf: &IndexSlice<I, T>, index: R) -> &T
where
    <T as thrust_models::Model>::Ty: PartialEq,
    <R as thrust_models::Model>::Ty: PartialEq,
{
    <IndexSlice<I, T> as std::ops::Index<R>>::index(slf, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(forall(|i: USize| <R as IntoSliceIdx<I, [T]>>::into_is(index, i) ==> i < (*slf).len()))]
#[thrust_macros::ensures(forall(|i: USize| <R as IntoSliceIdx<I, [T]>>::into_is(index, i)
    ==> (*result == (*slf)[i] && !slf == (*slf).store(i, !result))))]
fn _extern_spec_index_slice_index_mut<I: Idx + thrust_models::Model<Ty: PartialEq>, T: thrust_models::Model, R: IntoSliceIdx<I, [T], Output = usize> + thrust_models::Model>(slf: &mut IndexSlice<I, T>, index: R) -> &mut T
where
    <T as thrust_models::Model>::Ty: PartialEq,
    <R as thrust_models::Model>::Ty: PartialEq,
{
    <IndexSlice<I, T> as std::ops::IndexMut<R>>::index_mut(slf, index)
}
