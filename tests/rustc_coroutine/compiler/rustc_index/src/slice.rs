use crate::thrust_models;
use std::marker::PhantomData;
use std::slice::SliceIndex;

use thrust_models::forall;
use thrust_models::model::Seq;

use crate::rustc_index::{Idx, IdxRange, IndexVec, IntoSliceIdx};
use crate::case_study::USize;
use crate::IteratorSpec;

#[derive(PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexSlice<I: Idx, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: [T],
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
}

#[thrust_macros::context]
impl<'a, I: Idx + thrust_models::Model, T: thrust_models::Model> IteratorSpec for IterEnumerated<'a, I, T>
{
    // `next` builds `I::new(pos)`, so the invariant carries `can_new` of the positions left.
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.1 && self.1 <= self.0.len()
            && forall(|k: USize| !(self.1 <= k && k < self.0.len()) || <I as Idx>::can_new(k))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool {
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

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

// The last item of a sequence the iterator produces is the entry right after the items before it,
// with its index: a `Map` over the iterator reads its closure's `requires` at that item in
// `preservation_inv`, where the sequence is `s.push(e1).push(e2)`.
#[thrust_macros::context]
impl<'a, I: Idx + thrust_models::Model, T: thrust_models::Model> IterEnumerated<'a, I, T> {
    #[thrust_macros::ensures(forall(|s: Seq<<(I, &'a T) as thrust_models::Model>::Ty>, e: <(I, &'a T) as thrust_models::Model>::Ty, o: <Self as thrust_models::Model>::Ty|
        !<Self as IteratorSpec>::produces(*it, s.push(e), o)
            || ((*it).1 + s.len() < (*it).0.len()
                && <I as Idx>::index_is(e.0, (*it).1 + s.len())
                && e.1 == &(*it).0[(*it).1 + s.len()])))]
    #[thrust_macros::lemma]
    pub fn yields_last(it: &Self) {}
}

#[thrust_macros::context]
impl<I: Idx, T> IndexSlice<I, T> {
    // Trusted: the body is an unsafe cast through a raw pointer, which Thrust does not model.
    // `IndexSlice` is `repr(transparent)` over `[T]`, so the cast is the identity on the
    // sequence, which is what the contract says.
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(*result == *raw)]
    pub const fn from_raw(raw: &[T]) -> &Self {
        let ptr: *const [T] = raw;

        unsafe { &*(ptr as *const Self) }
    }

    // Trusted, as `from_raw`: an unsafe cast of the `&mut` through a raw pointer, the identity
    // on the sequence before and after the borrow.
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(*result == *raw && !result == !raw)]
    pub fn from_raw_mut(raw: &mut [T]) -> &mut Self {
        let ptr: *mut [T] = raw;

        unsafe { &mut *(ptr as *mut Self) }
    }

    #[inline]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == (*self).len())]
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
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.raw.iter()
    }

    #[inline]
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
    #[thrust_macros::ensures(result.start == 0 && result.end == (*self).len())]
    pub fn indices(&self) -> IdxRange<I> {
        let _ = I::new(self.len());
        IdxRange::new(0, self.len())
    }
}

#[thrust_macros::context]
impl<I: Idx, T: thrust_models::Model> IndexSlice<I, T>
{
    #[inline]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.0 == *self && result.1 == !self && result.2 == 0 && (!self).len() == (*self).len())]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.raw.iter_mut()
    }
}

#[thrust_macros::context]
impl<I: Idx + thrust_models::Model, J: Idx + thrust_models::Model> IndexSlice<I, J> {
    // `debug_assert_eq!` calls dropped (debug assertions are off; rewrites.md S6). The body
    // panics when an element is not below the length (`inverse[i2]`) or an index up to the length
    // cannot be built (`iter_enumerated`).
    #[thrust_macros::requires(forall(|k: USize| 0 <= k && k <= (*self).len() ==> <I as Idx>::can_new(k)))]
    #[thrust_macros::requires(forall(|k: USize, i: USize|
        0 <= k && k < (*self).len() && <J as Idx>::index_is((*self)[k], i) ==> i < (*self).len()))]
    // The inverse has the same length, and each entry is a position of `self` (or the `new(0)` it
    // starts from), so below the length.
    #[thrust_macros::ensures(result.len() == (*self).len())]
    #[thrust_macros::ensures(forall(|k: USize, i: USize|
        0 <= k && k < result.len() && <I as Idx>::index_is(result[k], i) ==> i < result.len()))]
    pub fn invert_bijective_mapping(&self) -> IndexVec<J, I> {
        let mut inverse = IndexVec::from_elem_n(Idx::new(0), self.len());
        for (i1, &i2) in self.iter_enumerated() {
            inverse[i2] = i1;
        }
        inverse
    }
}

impl<I: Idx, T: thrust_models::Model, R: IntoSliceIdx<I, [T]>> std::ops::Index<R> for IndexSlice<I, T> {
    type Output = <R::Output as SliceIndex<[T]>>::Output;

    #[inline]
    fn index(&self, index: R) -> &Self::Output {
        #[cfg(thrust_index_body_fail)]
        panic!();
        #[cfg(not(thrust_index_body_fail))]
        &self.raw[index.into_slice_idx()]
    }
}

impl<I: Idx, T: thrust_models::Model, R: IntoSliceIdx<I, [T]>> std::ops::IndexMut<R> for IndexSlice<I, T> {
    #[inline]
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        &mut self.raw[index.into_slice_idx()]
    }
}

// `Index`/`IndexMut` are foreign traits, so the contract is an extern spec. It covers the
// instances whose `R::Output` is `usize`, and the bodies are checked against it at each instance
// a call reaches. `IntoSliceIdx` has one impl, `I: Idx` into `usize`, through `Idx::index_logic`;
// the contracts name the position by `into_logic`, so no quantifier over positions needs an
// instance of `Idx`'s totality law.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(<R as IntoSliceIdx<I, [T]>>::into_logic(index) < (*slf).len())]
#[thrust_macros::ensures(*result == (*slf)[<R as IntoSliceIdx<I, [T]>>::into_logic(index)])]
fn _extern_spec_index_slice_index<I: Idx + thrust_models::Model, T: thrust_models::Model, R: IntoSliceIdx<I, [T], Output = usize> + thrust_models::Model>(slf: &IndexSlice<I, T>, index: R) -> &T
{
    <IndexSlice<I, T> as std::ops::Index<R>>::index(slf, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(<R as IntoSliceIdx<I, [T]>>::into_logic(index) < (*slf).len())]
#[thrust_macros::ensures(*result == (*slf)[<R as IntoSliceIdx<I, [T]>>::into_logic(index)]
    && !slf == (*slf).store(<R as IntoSliceIdx<I, [T]>>::into_logic(index), !result))]
fn _extern_spec_index_slice_index_mut<I: Idx + thrust_models::Model, T: thrust_models::Model, R: IntoSliceIdx<I, [T], Output = usize> + thrust_models::Model>(slf: &mut IndexSlice<I, T>, index: R) -> &mut T
{
    <IndexSlice<I, T> as std::ops::IndexMut<R>>::index_mut(slf, index)
}
