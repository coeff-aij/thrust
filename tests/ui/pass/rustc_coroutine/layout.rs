//@ignore-on-host: draft, stops at slice indexing by `IntoSliceIdx::Output` in the generic `Index` impl of `IndexSlice`, which has no specification (see README.md)
//@edition: 2024
#![feature(new_range_api)]
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:9799dfd7b THRUST_TRY_SPECS=1

// Extracted from tests/ui/pass/rustc_coroutine/target.rs (rustc's
// rustc_abi::layout::coroutine::layout, adapted). Stage 7 of the
// rustc_coroutine plan (README.md, "stage 7"). Everything `layout()` needs is
// copied verbatim, mostly from the already-annotated eligibility.rs (stage 5)
// and univariant.rs (stage 6, itself sourced from values.rs stage 1) rather
// than re-derived, for the same reason those two reuse bitset.rs/values.rs.
// This file is a DRAFT: it is not expected to verify (`ignore-on-host`
// above). `layout()` itself gets its panic-safety precondition (see the
// comment above it), plus `// TODO(proof):` comments at each panic site naming
// the fact that discharges it, plus a trusted `lemma_permutation_split`
// skeleton (not called from `layout()` yet).

use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost};

use std::borrow::{Borrow, BorrowMut};
use std::convert::TryInto;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Deref, DerefMut};
use std::range::RangeInclusive;
use std::slice::SliceIndex;
use std::{cmp, slice, vec};

// //== ./../rustc_hashes/src/lib.rs

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Hash64 {
    inner: u64,
}

impl Hash64 {
    pub const ZERO: Hash64 = Hash64 { inner: 0 };

    #[inline]
    pub fn new(n: u64) -> Self {
        Self { inner: n }
    }

    #[inline]
    pub fn as_u64(self) -> u64 {
        self.inner
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn wrapping_add(self, other: Self) -> Self {
        Self {
            inner: self.inner.wrapping_add(other.inner),
        }
    }
}

// //== ./../rustc_index/src/bit_set.rs (trusted family, from bitset.rs;
// `layout()` only needs the type `BitMatrix<LocalIdx, LocalIdx>` and
// `DenseBitSet<LocalIdx>` as opaque parameters/return types of
// `coroutine_saved_local_eligibility`, not their operations)

type Word = u64;

#[derive(/* Eq, PartialEq, */ Hash)]
pub struct DenseBitSet<T> {
    domain_size: usize,
    words: Vec<Word>,
    marker: PhantomData<T>,
}

#[thrust_macros::context]
impl<T: Idx> DenseBitSet<T> {
    /// `i` is a member of the set, as in bitset.rs.
    #[thrust_macros::predicate]
    fn mem(self, i: usize) -> bool {
        // self.words[i] != 0
        self.1[i] != 0
    }

    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::ensures(result.0 == (*self).0 && result.1 == 0)]
    #[thrust_macros::ensures(0 <= result.2 && result.2 <= (*self).0)]
    pub fn iter(&self) -> BitIter<'_, T> {
        BitIter::new(&self.words)
    }
}

pub struct WordIter<'a> {
    words: &'a [Word],
    pos: usize,
}

impl<'a> WordIter<'a> {
    fn new(words: &'a [Word]) -> WordIter<'a> {
        WordIter { words, pos: 0 }
    }
}

impl<'a> Iterator for WordIter<'a> {
    type Item = &'a Word;

    fn next(&mut self) -> Option<&'a Word> {
        if self.pos < self.words.len() {
            let item = &self.words[self.pos];
            self.pos += 1;
            Some(item)
        } else {
            None
        }
    }
}

pub struct BitIter<'a, T: Idx> {
    word: Word,
    offset: usize,
    iter: WordIter<'a>,
    marker: PhantomData<T>,
}

impl<'a, T: Idx> BitIter<'a, T> {
    #[thrust::trusted]
    #[thrust::callable]
    fn new(words: &'a [Word]) -> BitIter<'a, T> {
        BitIter {
            word: 0,
            offset: usize::MAX - (WORD_BITS - 1),
            iter: WordIter::new(words),
            marker: PhantomData,
        }
    }
}

const WORD_BYTES: usize = size_of::<Word>();
const WORD_BITS: usize = WORD_BYTES * 8;

impl<'a, T: Idx> Iterator for BitIter<'a, T> {
    type Item = T;
    #[thrust::trusted]
    #[thrust::callable]
    fn next(&mut self) -> Option<T> {
        loop {
            if self.word != 0 {
                let bit_pos = self.word.trailing_zeros() as usize;
                self.word ^= 1 << bit_pos;
                return Some(T::new(bit_pos + self.offset));
            }
            self.word = *self.iter.next()?;
            self.offset = self.offset.wrapping_add(WORD_BITS);
        }
    }
}

#[derive(/* Clone, Eq, PartialEq, */ Hash)]
pub struct BitMatrix<R: Idx, C: Idx> {
    num_rows: usize,
    num_columns: usize,
    words: Vec<Word>,
    marker: PhantomData<(R, C)>,
}

#[thrust_macros::context]
impl<R: Idx, C: Idx> BitMatrix<R, C> {
    /// Well-formedness, as in bitset.rs: `words` holds `num_words(num_columns)` words per row.
    #[thrust_macros::predicate]
    fn wf(self) -> bool {
        exists(|rw: Int| {
            self.words.len() == self.num_rows * rw
                && 64 * rw >= self.num_columns
                && 64 * rw < self.num_columns + 64
        })
    }

    #[thrust::trusted]
    #[thrust_macros::ensures(result.start == 0)]
    #[thrust_macros::ensures(result.end == (*self).num_rows)]
    pub fn rows(&self) -> IdxRange<R> {
        IdxRange::new(0, self.num_rows)
    }

    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(forall(|i: Int| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    #[thrust_macros::ensures(result.0 <= result.1)]
    #[thrust_macros::ensures(result.1 <= (*self).words.len())]
    fn range(&self, row: R) -> (usize, usize) {
        let words_per_row = num_words(self.num_columns);
        let start = row.index() * words_per_row;
        (start, start + words_per_row)
    }

    #[thrust::trusted]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(forall(|i: Int| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    #[thrust_macros::ensures(result.0 == (*self).num_columns && result.1 == 0)]
    #[thrust_macros::ensures(0 <= result.2 && result.2 <= (*self).num_columns)]
    pub fn iter(&self, row: R) -> BitIter<'_, C> {
        assert!(row.index() < self.num_rows);
        let (start, end) = self.range(row);
        BitIter::new(&self.words[start..end])
    }

    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(forall(|i: Int| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    pub fn count(&self, row: R) -> usize {
        let (start, end) = self.range(row);
        count_ones(&self.words[start..end])
    }
}

#[thrust::trusted]
#[thrust::callable]
fn num_words<T: Idx>(domain_size: T) -> usize {
    domain_size.index().div_ceil(WORD_BITS)
}

#[thrust::trusted]
#[thrust::callable]
fn count_ones(words: &[Word]) -> usize {
    words.iter().map(|word| word.count_ones() as usize).sum()
}

// //== ./../rustc_index/src/idx.rs (from bitset.rs / univariant.rs)

#[thrust_macros::context]
pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    #[thrust_macros::predicate]
    fn index_is(self, i: usize) -> bool;

    #[thrust_macros::predicate]
    fn can_new(idx: usize) -> bool;

    #[thrust_macros::requires(Self::can_new(idx))]
    #[thrust_macros::ensures(Self::index_is(result, idx))]
    fn new(idx: usize) -> Self;

    #[thrust_macros::ensures(Self::index_is(self, result))]
    fn index(self) -> usize;

    #[inline]
    #[thrust_macros::requires(forall(|i: Int, a: Int|
        Self::index_is(*self, i) && a == amount ==> Self::can_new(i + a)))]
    fn increment_by(&mut self, amount: usize) {
        *self = self.plus(amount);
    }

    #[inline]
    #[must_use = "Use `increment_by` if you wanted to update the index in-place"]
    #[thrust_macros::requires(forall(|i: Int, a: Int|
        Self::index_is(self, i) && a == amount ==> Self::can_new(i + a)))]
    fn plus(self, amount: usize) -> Self {
        Self::new(self.index() + amount)
    }
}

#[thrust_macros::context]
impl Idx for usize {
    #[thrust_macros::predicate]
    fn index_is(self, i: usize) -> bool {
        // i == self
        i == self
    }

    #[thrust_macros::predicate]
    fn can_new(idx: usize) -> bool {
        true
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

// `in_memory_order: IndexVec<u32, FieldIdx>` needs `u32: Idx`; idx.rs verifies these bodies.
#[thrust_macros::context]
impl Idx for u32 {
    #[thrust_macros::predicate]
    fn index_is(self, i: usize) -> bool {
        // i == self
        i == self
    }

    #[thrust_macros::predicate]
    fn can_new(idx: usize) -> bool {
        // idx <= u32::MAX
        idx <= 4294967295usize
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

/// Own iterator standing in for `(start..end).map(I::new)`.
pub struct IdxRange<I: Idx> {
    start: usize,
    end: usize,
    marker: PhantomData<I>,
}

impl<I: Idx> IdxRange<I> {
    fn new(start: usize, end: usize) -> IdxRange<I> {
        IdxRange {
            start,
            end,
            marker: PhantomData,
        }
    }
}

impl<I: Idx> Iterator for IdxRange<I> {
    type Item = I;

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

#[thrust_macros::context]
impl<I: Idx> IdxRange<I> {
    // idx.rs's contract of `next`.
    #[thrust::extern_spec_fn]
    #[thrust_macros::requires((*it).start >= 0)]
    #[thrust_macros::requires(
        forall(|s: Int| s == (*it).start && s < (*it).end ==> <I as Idx>::can_new(s))
    )]
    #[thrust_macros::ensures(
        forall(|s: Int| s == (*it).start && s < (*it).end
            ==> exists(|x: <I as thrust_models::Model>::Ty|
                    result == Some(x) && <I as Idx>::index_is(x, s))
                && s + 1 == (!it).start
                && (!it).end == (*it).end)
    )]
    #[thrust_macros::ensures(
        !((*it).start < (*it).end)
            ==> result == None && (!it).start == (*it).start && (!it).end == (*it).end
    )]
    fn _extern_spec_next(it: &mut IdxRange<I>) -> Option<I>
    where
        I: thrust_models::Model,
        <I as thrust_models::Model>::Ty: PartialEq,
    {
        <IdxRange<I> as Iterator>::next(it)
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

// //== ./../rustc_index/src/slice.rs (from eligibility.rs / univariant.rs)

// `PartialEq, Eq` commented out: the derived `eq` compares the `PhantomData`
// field, whose model is the unit sort, and Thrust panics with
// `unbound var $0` -- the same reason bitset.rs drops them from `DenseBitSet`.
#[derive(/* PartialEq, Eq, */ Hash)]
#[repr(transparent)]
pub struct IndexSlice<I: Idx, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: [T],
}

pub struct SliceIter<'a, T> {
    raw: &'a [T],
    pos: usize,
}

impl<'a, T> Iterator for SliceIter<'a, T> {
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
}

pub struct IterEnumerated<'a, I: Idx, T> {
    raw: &'a [T],
    pos: usize,
    marker: PhantomData<I>,
}

impl<'a, I: Idx, T> Iterator for IterEnumerated<'a, I, T> {
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

    // The iterator builds `I::new(k)` for every position `k` below the length, so the
    // precondition covers them, which `IterEnumerated`'s invariant then carries.
    #[inline]
    #[thrust_macros::requires(forall(|k: Int| !(0 <= k && k <= (*self).len()) || <I as Idx>::can_new(k)))]
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

    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.raw.iter_mut()
    }
}

#[thrust_macros::context]
impl<I: Idx + thrust_models::Model<Ty: PartialEq>, J: Idx> IndexSlice<I, J> {
    // `debug_assert_eq!` calls dropped (debug assertions are off). The body panics when an
    // element is not below the length (`inverse[i2]`) or an index up to the length cannot be
    // built (`iter_enumerated`).
    #[thrust_macros::requires(forall(|k: Int| !(0 <= k && k <= (*self).len()) || <I as Idx>::can_new(k)))]
    #[thrust_macros::requires(forall(|k: Int, i: Int|
        !(0 <= k && k < (*self).len() && <J as Idx>::index_is((*self)[k], i)) || i < (*self).len()))]
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
#[thrust_macros::requires(forall(|i: Int| <R as IntoSliceIdx<I, [T]>>::into_is(index, i) ==> i < (*slf).len()))]
#[thrust_macros::ensures(forall(|i: Int| <R as IntoSliceIdx<I, [T]>>::into_is(index, i) ==> *result == (*slf)[i]))]
fn _extern_spec_index_slice_index<I: Idx + thrust_models::Model<Ty: PartialEq>, T: thrust_models::Model, R: IntoSliceIdx<I, [T], Output = usize> + thrust_models::Model>(slf: &IndexSlice<I, T>, index: R) -> &T
where
    <T as thrust_models::Model>::Ty: PartialEq,
    <R as thrust_models::Model>::Ty: PartialEq,
{
    <IndexSlice<I, T> as std::ops::Index<R>>::index(slf, index)
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(forall(|i: Int| <R as IntoSliceIdx<I, [T]>>::into_is(index, i) ==> i < (*slf).len()))]
#[thrust_macros::ensures(forall(|i: Int| <R as IntoSliceIdx<I, [T]>>::into_is(index, i)
    ==> (*result == (*slf)[i] && !result == (!slf)[i] && (!slf).len() == (*slf).len())))]
fn _extern_spec_index_slice_index_mut<I: Idx + thrust_models::Model<Ty: PartialEq>, T: thrust_models::Model, R: IntoSliceIdx<I, [T], Output = usize> + thrust_models::Model>(slf: &mut IndexSlice<I, T>, index: R) -> &mut T
where
    <T as thrust_models::Model>::Ty: PartialEq,
    <R as thrust_models::Model>::Ty: PartialEq,
{
    <IndexSlice<I, T> as std::ops::IndexMut<R>>::index_mut(slf, index)
}

// //== ./../rustc_index/src/vec.rs (from eligibility.rs / univariant.rs)

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexVec<I: Idx, T> {
    pub raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

#[thrust_macros::context]
impl<I: Idx, T> IndexVec<I, T> {
    #[inline]
    pub const fn new() -> Self {
        IndexVec::from_raw(Vec::new())
    }

    #[inline]
    pub const fn from_raw(raw: Vec<T>) -> Self {
        IndexVec {
            raw,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn from_elem<S>(elem: T, universe: &IndexSlice<I, S>) -> Self
    where
        T: Clone,
    {
        IndexVec::from_raw(vec![elem; universe.len()])
    }

    #[inline]
    #[thrust_macros::ensures(result.len() == n
        && forall(|k: Int| !(0 <= k && k < n) || result[k] == elem))]
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

    #[inline]
    #[thrust_macros::requires(<I as Idx>::can_new((*self).len()))]
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

#[thrust_macros::context]
impl<I: Idx, T> IntoIteratorSpec for IndexVec<I, T>
where
    I: thrust_models::Model,
    I::Ty: PartialEq,
    T: thrust_models::Model,
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn into_iter_is(self, it: vec::IntoIter<T>) -> bool {
        it.0 == self && it.1 == 0
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a IndexVec<I, T> {
    type Item = &'a T;
    type IntoIter = SliceIter<'a, T>;

    #[inline]
    fn into_iter(self) -> SliceIter<'a, T> {
        self.iter()
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a mut IndexVec<I, T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<I: Idx, T, const N: usize> From<[T; N]> for IndexVec<I, T> {
    #[inline]
    fn from(array: [T; N]) -> Self {
        IndexVec::from_raw(array.into())
    }
}

// //== ./src/layout/coroutine.rs: `coroutine_saved_local_eligibility` (from
// eligibility.rs, stage 5)

#[derive(Clone, /*Debug,*/ PartialEq)]
enum SavedLocalEligibility<VariantIdx, FieldIdx> {
    Unassigned,
    Assigned(VariantIdx),
    Ineligible(Option<FieldIdx>),
}

// Trusted stub here: this file only calls it. The contract is eligibility.rs's (stage 5), which
// that file checks against the body.
#[thrust::trusted]
#[thrust_macros::requires(
    forall(|v: usize, f: usize|
        !(0 <= v && v < (*variant_fields).len()
            && 0 <= f && f < (*variant_fields)[v].len())
        || forall(|i: Int|
            !<LocalIdx as Idx>::index_is((*variant_fields)[v][f], i)
                || i < nb_locals))
    // `count(local_b)` takes a column index as a row, so the columns must not outnumber the
    // rows: the set abstraction does not say which bits a row holds, so this is stronger than
    // the panic condition (a set bit of some row at a column >= num_rows).
    && (*storage_conflicts).num_rows <= nb_locals
    && (*storage_conflicts).num_columns <= (*storage_conflicts).num_rows
    && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
    && forall(|k: Int| !(0 <= k && k < nb_locals) || LocalIdx::can_new(k))
    && forall(|n: Int| !(0 <= n && n <= nb_locals) || FieldIdx::can_new(n))
    && forall(|v: Int| !(0 <= v && v <= (*variant_fields).len()) || VariantIdx::can_new(v))
)]
#[thrust_macros::ensures(
    // `assignments` has one entry per local, and `inel` is a set over the locals, so its
    // iterator yields locals below `nb_locals`.
    result.1.len() == nb_locals
    && result.0.0 == nb_locals
    // 1. Unassigned locals never appear in any variant's field list.
    && forall(|l: usize| !(0 <= l && l < nb_locals && result.1[l] == SavedLocalEligibility::Unassigned)
        || forall(|v: usize, f: usize|
            !(0 <= v && v < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[v].len())
            || !thrust_models::exists(|i: Int|
                i == l
                    && <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i))))
    // 2. Assigned(v) locals appear only under variant v, and only there.
    // TODO(spec): "exists f: variant_fields[v][f] == l" and the "not under
    // any other assigned variant" half are folded into one nested forall/
    // exists below; the exact quantifier shape is a best effort, not
    // checked against the solver (this file does not verify, see header).
    && forall(|l: usize, v: usize|
        !(0 <= l && l < nb_locals
            && thrust_models::exists(|vi: <VariantIdx as thrust_models::Model>::Ty|
                thrust_models::exists(|vn: Int| vn == v && <VariantIdx as Idx>::index_is(vi, vn))
                    && result.1[l] == SavedLocalEligibility::Assigned(vi)))
        || (v < (*variant_fields).len()
            && thrust_models::exists(|f: usize|
                0 <= f && f < (*variant_fields)[v].len()
                    && thrust_models::exists(|i: Int|
                        i == l
                            && <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i)))))
    // 3. An ineligible local has its promoted field index. The README bounds it by the
    // cardinality of `inel`, which no predicate states yet (DenseBitSet cardinality); the bound
    // stated is the number of locals, which the cardinality is at most.
    && forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
        !(0 <= l && l < nb_locals && result.1[l] == SavedLocalEligibility::Ineligible(x))
        || thrust_models::exists(|k: <FieldIdx as thrust_models::Model>::Ty|
            x == Some(k) && forall(|i: Int| !<FieldIdx as Idx>::index_is(k, i) || i < nb_locals)))
    // 4. Membership in `inel` matches being `Ineligible(_)`.
    // TODO(spec): `DenseBitSet::elem_at`/`mem` are uninterpreted here, see
    // above; written as an `<==>` via two `==>` for the annotation grammar.
    // `mem` takes an `Int` (its declared `usize` parameter is lowered to
    // `Int` by `#[thrust_macros::predicate]`, see the note above the
    // `requires`), but real `Vec` indexing needs a literal `usize`; the
    // `exists(|li: Int| li == l && ..)` below is a `usize -> Int` bridge
    // (`Int: PartialEq<T> where T: Model<Ty = Int>`, and `usize` is one).
    && forall(|l: usize| !(0 <= l && l < nb_locals) ||
        (!thrust_models::exists(|li: Int| li == l && DenseBitSet::<LocalIdx>::mem(result.0, li))
            || thrust_models::exists(|x: Option<<FieldIdx as thrust_models::Model>::Ty>| result.1[l] == SavedLocalEligibility::Ineligible(x))))
    && forall(|l: usize| !(0 <= l && l < nb_locals) ||
        (!thrust_models::exists(|x: Option<<FieldIdx as thrust_models::Model>::Ty>| result.1[l] == SavedLocalEligibility::Ineligible(x))
            || thrust_models::exists(|li: Int| li == l && DenseBitSet::<LocalIdx>::mem(result.0, li))))
)]
#[thrust_macros::context]
fn coroutine_saved_local_eligibility<VariantIdx: Idx, FieldIdx: Idx, LocalIdx: Idx>(
    nb_locals: usize,
    variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>,
    storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>,
) -> (
    DenseBitSet<LocalIdx>,
    IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
) {
    unimplemented!()
}

// //== ./src/layout/coroutine.rs: `layout()` itself (verbatim)
//
// Precondition (experiments/2026-10-01-layout-precondition-review.md), with n the number of
// saved locals (`local_layouts.len()`), V the number of variants and P the number of prefix
// layouts:
// - V > 0, which rustc's caller has by construction (V = 3 + the number of yields);
// - `storage_conflicts` is well formed, has at most n rows, and no more columns than rows
//   (eligibility's `count(local_b)` reads a column index as a row; see eligibility.rs);
// - every local a variant lists is below n;
// - the index types can be built wherever `new` is called: `LocalIdx` below n, `VariantIdx` up
//   to V (`iter_enumerated` builds `new(V)`), `FieldIdx` up to P + 1 + n (the prefix, the tag
//   and at most n promoted locals) and up to each variant's length (a variant may list a local
//   twice);
// - P + 1 + n <= u32::MAX, for the `u32` memory order.
// Not stated: `dl_wf` of the data layout, and `niche_wf` of every input layout and of
// `tag_to_layout(tag)`. The data layout is reached through the generic `Cx::data_layout()`, and
// the closure's result is an `F`, whose model is not related to the `LayoutData` it
// dereferences to.
#[thrust_macros::requires(
    (*variant_fields).len() > 0
        && (*storage_conflicts).num_rows <= (*local_layouts).len()
        && (*storage_conflicts).num_columns <= (*storage_conflicts).num_rows
        && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
        && forall(|v: usize, f: usize|
            !(0 <= v && v < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[v].len())
            || forall(|i: Int|
                !<LocalIdx as Idx>::index_is((*variant_fields)[v][f], i)
                    || i < (*local_layouts).len()))
        && forall(|k: Int| !(0 <= k && k < (*local_layouts).len()) || <LocalIdx as Idx>::can_new(k))
        && forall(|k: Int| !(0 <= k && k <= (*variant_fields).len()) || <VariantIdx as Idx>::can_new(k))
        && forall(|k: Int|
            !(0 <= k && k <= prefix_layouts.len() + 1 + (*local_layouts).len())
                || <FieldIdx as Idx>::can_new(k))
        && forall(|v: usize, k: Int|
            !(0 <= v && v < (*variant_fields).len() && 0 <= k && k <= (*variant_fields)[v].len())
                || <FieldIdx as Idx>::can_new(k))
        && prefix_layouts.len() + 1 + (*local_layouts).len() <= 4294967295usize
)]
#[thrust_macros::ensures(true)]
pub fn layout<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy + PartialEq + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    LocalIdx: Idx + thrust_models::Model<Ty: PartialEq>,
>(
    calc: &LayoutCalculator<impl HasDataLayout>,
    local_layouts: &IndexSlice<LocalIdx, F>,
    mut prefix_layouts: IndexVec<FieldIdx, F>,
    variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>,
    storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>,
    tag_to_layout: impl Fn(Scalar) -> F,
) -> LayoutCalculatorResult<FieldIdx, VariantIdx, F> {
    use SavedLocalEligibility::*;

    let (ineligible_locals, assignments) =
        coroutine_saved_local_eligibility(local_layouts.len(), variant_fields, storage_conflicts);

    let tag_index = prefix_layouts.next_index();

    // `variant_fields.len() > 0` (the precondition) keeps the subtraction from wrapping.
    let max_discr = (variant_fields.len() - 1) as u128;
    let discr_int = Integer::fit_unsigned(max_discr);
    let tag = Scalar::Initialized {
        value: Primitive::Int(discr_int, false),
        valid_range: WrappingRange {
            start: 0,
            end: max_discr,
        },
    };

    // Rewrite (rewrites.md R8): `Map::new(it, f)` for `it.map(f)`, `extend_from` for `extend`.
    let promoted_layouts = Map::new(ineligible_locals.iter(), |local| local_layouts[local]);
    prefix_layouts.push(tag_to_layout(tag));
    prefix_layouts.extend_from(promoted_layouts);
    // TODO(proof): `push` and `extend_from` give `prefix_layouts.len() == P + 1 + c`, c the
    // items `ineligible_locals.iter()` yields, at most n by `BitIter`'s model; `c ==
    // card(ineligible_locals)` needs the set cardinality, which no predicate states yet.
    let prefix = match calc.univariant(
        &prefix_layouts,
        &ReprOptions::default(),
        StructKind::AlwaysSized,
    ) {
        Ok(prefix) => prefix,
        Err(err) => return Err(err),
    };

    let (prefix_size, prefix_align) = (prefix.size, prefix.align);

    let (outer_fields, promoted_offsets, promoted_memory_index) = match prefix.fields {
        FieldsShape::Arbitrary {
            mut offsets,
            in_memory_order,
        } => {
            let b_start = tag_index.plus(1);
            // TODO(proof): `split_off(b_start.index())` needs `b_start.index()
            // <= offsets.raw.len()`: `offsets` has `prefix_layouts.len()`
            // entries (univariant's `arbitrary_of`), which is at least
            // `tag_index + 1` (the prefix-length fact above).
            let offsets_b = IndexVec::from_raw(offsets.raw.split_off(b_start.index()));
            let offsets_a = offsets;

            let mut in_memory_order_a = IndexVec::<u32, FieldIdx>::new();
            let mut in_memory_order_b = IndexVec::<u32, FieldIdx>::new();
            let mut in_memory_order_iter = in_memory_order.into_iter();
            while let Some(i) = in_memory_order_iter.next() {
                if let Some(j) = i.index().checked_sub(b_start.index()) {
                    in_memory_order_b.push(FieldIdx::new(j));
                } else {
                    in_memory_order_a.push(i);
                }
            }

            let outer_fields = FieldsShape::Arbitrary {
                offsets: offsets_a,
                in_memory_order: in_memory_order_a,
            };
            (
                outer_fields,
                offsets_b,
                // TODO(proof): `invert_bijective_mapping` requires every
                // element of `in_memory_order_b` below its length -- the
                // permutation-split fact `lemma_permutation_split` below
                // gives it from univariant's `arbitrary_of`; not called yet.
                in_memory_order_b.invert_bijective_mapping(),
            )
        }
        _ => unreachable!(), // TODO(proof): unreachable by univariant's ensures (`arbitrary_of`).
    };

    let mut size = prefix.size;
    let mut align = prefix.align;
    // Rewrite (rewrites.md R8): `Map::new(it, f)` for `it.map(f)` and `Filter::new(it, p)` for
    // `it.filter(p)` here and below, and `collect_index_vec_result` for the `collect` at the end
    // of this expression.
    let variants = collect_index_vec_result::<VariantIdx, _, _, _>(Map::new(
        variant_fields.iter_enumerated(),
        |(index, variant_fields)| {
            let variant_only_tys = Map::new(
                Filter::new(variant_fields.iter(), |local| match assignments[**local] {
                    // TODO(proof): unreachable by eligibility.rs's stage-5
                    // property 1 (an `Unassigned` local never appears in any
                    // variant's field list).
                    Unassigned => unreachable!(),
                    Assigned(v) if v == index => true,
                    // TODO(proof): unreachable by property 2 (`Assigned(v)`
                    // appears only under variant `v`).
                    Assigned(_) => unreachable!(),
                    Ineligible(_) => false,
                }),
                |local| local_layouts[*local],
            );

            // Rewrite (rewrites.md R8): `collect_index_vec` for `collect`.
            let mut variant = match calc.univariant(
                &collect_index_vec(variant_only_tys),
                &ReprOptions::default(),
                StructKind::Prefixed(prefix_size, prefix_align.abi),
            ) {
                Ok(variant) => variant,
                Err(err) => return Err(err),
            };

            let FieldsShape::Arbitrary {
                offsets,
                in_memory_order,
            } = variant.fields
            else {
                unreachable!(); // TODO(proof): same as the prefix's, above.
            };

            let memory_index = in_memory_order.invert_bijective_mapping();
            let invalid_field_idx = promoted_memory_index.len() + memory_index.len();
            let mut combined_in_memory_order =
                IndexVec::from_elem_n(FieldIdx::new(invalid_field_idx), invalid_field_idx);

            let mut offsets_and_memory_index = iter::zip(offsets, memory_index);
            // Rewrite (rewrites.md R8): `Map::new` and `collect_index_vec` for `map` and `collect`.
            let combined_offsets = collect_index_vec(Map::new(
                variant_fields.iter_enumerated(),
                |(i, local)| {
                    let (offset, memory_index) = match assignments[*local] {
                        Unassigned => unreachable!(), // TODO(proof): as above.
                        Assigned(_) => {
                            // TODO(proof): `.unwrap()` needs
                            // `offsets_and_memory_index` to have as many
                            // entries left as there are `Assigned` locals
                            // still to visit -- README stage 7, "the number of Assigned
                            // equals the length of variant_only_tys".
                            let (offset, memory_index) = offsets_and_memory_index.next().unwrap();
                            (offset, promoted_memory_index.len() as u32 + memory_index)
                        }
                        Ineligible(field_idx) => {
                            // TODO(proof): `.unwrap()` needs `field_idx ==
                            // Some(_)` -- eligibility.rs's stage-5 property 3.
                            let field_idx = field_idx.unwrap();
                            (
                                // TODO(proof): needs `field_idx <
                                // card(ineligible_locals) == offsets_b.len()`
                                // -- README stage 7.
                                promoted_offsets[field_idx],
                                promoted_memory_index[field_idx],
                            )
                        }
                    };
                    // TODO(proof): `combined_in_memory_order[memory_index]`
                    // needs `promoted_memory_index.len() + memory_index <
                    // invalid_field_idx` -- README stage 7 (memory_index is a
                    // permutation's inverse, so `< len`; promoted_memory_index
                    // entries are likewise `< len`).
                    combined_in_memory_order[memory_index] = i;
                    offset
                },
            ));

            combined_in_memory_order
                .raw
                .retain(|&i| i.index() != invalid_field_idx);

            variant.fields = FieldsShape::Arbitrary {
                offsets: combined_offsets,
                in_memory_order: combined_in_memory_order,
            };

            size = size.max(variant.size);
            align = align.max(variant.align);
            // TODO(proof): `VariantLayout::from_layout`'s own panic is
            // unreachable because `variant.fields` was just reassigned to
            // `Arbitrary` above (README stage 7, "unreachable").
            Ok(VariantLayout::from_layout(variant))
        },
    ))?;

    size = size.align_to(align.abi);

    // Rewrite (rewrites.md R8): `iter_all(it, f)` for `it.all(f)`.
    let uninhabited = prefix.uninhabited || iter_all(variants.iter(), |v| v.is_uninhabited());
    let abi = BackendRepr::Memory { sized: true };

    Ok(LayoutData {
        variants: Variants::Multiple {
            tag,
            tag_encoding: TagEncoding::Direct,
            tag_field: tag_index,
            variants,
        },
        fields: outer_fields,
        backend_repr: abi,

        largest_niche: None,
        uninhabited,
        size,
        align,
        max_repr_align: None,
        unadjusted_abi_align: align.abi,
        randomization_seed: Default::default(),
    })
}

// //== stage 7 trusted lemma skeleton (README.md, stage 7): "a/b split" fact.
// Not called from `layout()` above (per the task); left as a skeleton for a
// later session to wire in at the `invert_bijective_mapping` call site noted
// with a TODO(proof) above.
//
// If `order` is a permutation of `0..n` (an `IndexVec<u32, FieldIdx>` of
// length `n`, injective, all values `< n`), then the sub-sequence of it at or
// above `b_start` (`order_b`, built the same way `layout()` builds
// `in_memory_order_b`: `order[k] - b_start` for each `order[k] >= b_start`)
// has exactly `n - b_start` entries, and those entries are themselves a
// permutation of `0..n - b_start`.
// An element of the shared `(array, length)` model is
// `<FieldIdx as Model>::Ty`, not a real `FieldIdx`, so `Idx::index()` is not
// callable on it; `Idx::index_is` carries the same fact.
#[thrust::trusted]
#[thrust_macros::requires(
    order.len() == n
        && forall(|k: usize, i: Int|
            !(0 <= k && k < n && <FieldIdx as Idx>::index_is(order[k], i))
                || i < n)
        && forall(|k: usize, k2: usize, i: Int|
            !(0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2)
                && <FieldIdx as Idx>::index_is(order[k], i))
                || !<FieldIdx as Idx>::index_is(order[k2], i))
        && b_start <= n
)]
#[thrust_macros::ensures(
    result.len() == n - b_start
        && forall(|k: usize, i: Int|
            !(0 <= k && k < result.len() && <FieldIdx as Idx>::index_is(result[k], i))
                || i < n - b_start)
        && forall(|k: usize, k2: usize, i: Int|
            !(0 <= k && k < result.len() && 0 <= k2 && k2 < result.len() && !(k == k2)
                && <FieldIdx as Idx>::index_is(result[k], i))
                || !<FieldIdx as Idx>::index_is(result[k2], i))
)]
fn lemma_permutation_split<FieldIdx: Idx>(
    order: IndexVec<u32, FieldIdx>,
    n: usize,
    b_start: usize,
) -> IndexVec<u32, FieldIdx> {
    unimplemented!()
}

// //== value types (from univariant.rs / values.rs, verbatim)

#[derive(Copy, Clone, /*Debug,*/ PartialEq, Eq)]
pub struct PointerSpec {
    pointer_size: Size,
    pointer_align: Align,
    pointer_offset: Size,
    _is_fat: bool,
}

#[derive(/*Debug,*/ /*PartialEq, Eq*/)]
pub struct TargetDataLayout {
    pub endian: Endian,
    pub i1_align: Align,
    pub i8_align: Align,
    pub i16_align: Align,
    pub i32_align: Align,
    pub i64_align: Align,
    pub i128_align: Align,
    pub f16_align: Align,
    pub f32_align: Align,
    pub f64_align: Align,
    pub f128_align: Align,
    pub aggregate_align: Align,
    pub vector_align: Vec<(Size, Align)>,
    pub default_address_space: AddressSpace,
    pub default_address_space_pointer_spec: PointerSpec,
    address_space_info: Vec<(AddressSpace, PointerSpec)>,
    pub instruction_address_space: AddressSpace,
    pub c_enum_min_size: Integer,
}

#[thrust_macros::context]
impl TargetDataLayout {
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(((*self).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 8))]
    #[thrust_macros::ensures(result >= 1)]
    pub fn obj_size_bound(&self) -> u64 {
        match self.pointer_size().bits() {
            16 => 1 << 15,
            32 => 1 << 31,
            64 => 1 << 61,
            bits => panic!("obj_size_bound: unknown pointer bit size {bits}"),
        }
    }

    #[inline]
    pub fn pointer_size(&self) -> Size {
        self.default_address_space_pointer_spec.pointer_size
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(((*self).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 8)
        && c == (*self).default_address_space)]
    #[thrust_macros::ensures(true)]
    pub fn pointer_size_in(&self, c: AddressSpace) -> Size {
        if c == self.default_address_space {
            return self.default_address_space_pointer_spec.pointer_size;
        }
        if let Some(e) = self.address_space_info.iter().find(|(a, _)| a == &c) {
            e.1.pointer_size
        } else {
            panic!("Use of unknown address space");
        }
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(((*self).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*self).default_address_space_pointer_spec.pointer_size.raw == 8)
        && c == (*self).default_address_space)]
    #[thrust_macros::ensures(true)]
    pub fn pointer_align_in(&self, c: AddressSpace) -> AbiAlign {
        AbiAlign::new(if c == self.default_address_space {
            self.default_address_space_pointer_spec.pointer_align
        } else if let Some(e) = self.address_space_info.iter().find(|(a, _)| a == &c) {
            e.1.pointer_align
        } else {
            panic!("Use of unknown address space");
        })
    }
}

pub trait HasDataLayout {
    fn data_layout(&self) -> &TargetDataLayout;
}

impl HasDataLayout for TargetDataLayout {
    #[inline]
    fn data_layout(&self) -> &TargetDataLayout {
        self
    }
}

impl HasDataLayout for &TargetDataLayout {
    #[inline]
    fn data_layout(&self) -> &TargetDataLayout {
        (**self).data_layout()
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Endian {
    Little,
    Big,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Size {
    raw: u64,
}

#[thrust_macros::context]
impl Size {
    pub const ZERO: Size = Size { raw: 0 };

    #[thrust_macros::requires(T::fits(bits))]
    #[thrust_macros::ensures(thrust_models::exists(|b| T::converts_to(bits, b) && result.raw == (b + 7) / 8))]
    pub fn from_bits<T: TryIntoSpec<u64>>(bits: T) -> Size {
        let bits = bits.try_into().ok().unwrap();
        Size {
            raw: bits.div_ceil(8),
        }
    }

    #[inline]
    #[thrust_macros::requires(T::fits(bytes))]
    #[thrust_macros::ensures(thrust_models::exists(|b| T::converts_to(bytes, b) && result.raw == b))]
    pub fn from_bytes<T: TryIntoSpec<u64>>(bytes: T) -> Size {
        let bytes: u64 = bytes.try_into().ok().unwrap();
        Size { raw: bytes }
    }

    #[inline]
    pub fn bytes(self) -> u64 {
        self.raw
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::ensures(result == self.raw * 8)]
    pub fn bits(self) -> u64 {
        #[cold]
        #[thrust::trusted]
        #[thrust::callable]
        fn overflow(bytes: u64) -> ! {
            panic!("Size::bits: {bytes} bytes in bits doesn't fit in u64")
        }

        self.bytes()
            .checked_mul(8)
            .unwrap_or_else(|| overflow(self.bytes()))
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn align_to(self, align: Align) -> Size {
        let mask = align.bytes() - 1;
        Size::from_bytes((self.bytes() + mask) & !mask)
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn checked_add<C: HasDataLayout>(self, offset: Size, cx: &C) -> Option<Size> {
        let dl = cx.data_layout();
        let bytes = self.bytes().checked_add(offset.bytes())?;
        if bytes < dl.obj_size_bound() {
            Some(Size::from_bytes(bytes))
        } else {
            None
        }
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn unsigned_int_max(&self) -> u128 {
        u128::MAX >> (128 - self.bits())
    }
}

impl Add for Size {
    type Output = Size;
    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    fn add(self, other: Size) -> Size {
        Size::from_bytes(self.bytes().checked_add(other.bytes()).unwrap_or_else(|| {
            panic!(
                "Size::add: {} + {} doesn't fit in u64",
                self.bytes(),
                other.bytes()
            )
        }))
    }
}

impl AddAssign for Size {
    #[inline]
    fn add_assign(&mut self, other: Size) {
        *self = *self + other;
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Align {
    pow2: u8,
}

#[thrust_macros::context]
impl Align {
    pub const ONE: Align = Align { pow2: 0 };
    pub const EIGHT: Align = Align { pow2: 3 };
    pub const MAX: Align = Align { pow2: 29 };

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::ensures(result >= 1)]
    pub const fn bytes(self) -> u64 {
        1 << self.pow2
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash /*Debug*/)]
pub struct AbiAlign {
    pub abi: Align,
}

impl AbiAlign {
    #[inline]
    pub fn new(align: Align) -> AbiAlign {
        AbiAlign { abi: align }
    }
    #[inline]
    pub fn min(self, other: AbiAlign) -> AbiAlign {
        AbiAlign {
            abi: self.abi.min(other.abi),
        }
    }
    #[inline]
    pub fn max(self, other: AbiAlign) -> AbiAlign {
        AbiAlign {
            abi: self.abi.max(other.abi),
        }
    }
}

impl Deref for AbiAlign {
    type Target = Align;
    fn deref(&self) -> &Self::Target {
        &self.abi
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash /*Debug*/)]
pub enum Integer {
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[thrust_macros::context]
impl Integer {
    #[inline]
    pub fn size(self) -> Size {
        use Integer::*;
        match self {
            I8 => Size::from_bytes(1),
            I16 => Size::from_bytes(2),
            I32 => Size::from_bytes(4),
            I64 => Size::from_bytes(8),
            I128 => Size::from_bytes(16),
        }
    }

    pub fn align<C: HasDataLayout>(self, cx: &C) -> AbiAlign {
        use Integer::*;
        let dl = cx.data_layout();
        AbiAlign::new(match self {
            I8 => dl.i8_align,
            I16 => dl.i16_align,
            I32 => dl.i32_align,
            I64 => dl.i64_align,
            I128 => dl.i128_align,
        })
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn fit_unsigned(x: u128) -> Integer {
        use Integer::*;
        match x {
            0..=0x0000_0000_0000_00ff => I8,
            0..=0x0000_0000_0000_ffff => I16,
            0..=0x0000_0000_ffff_ffff => I32,
            0..=0xffff_ffff_ffff_ffff => I64,
            _ => I128,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash /*Debug*/)]
pub enum Float {
    F16,
    F32,
    F64,
    F128,
}

#[thrust_macros::context]
impl Float {
    pub fn size(self) -> Size {
        use Float::*;
        match self {
            F16 => Size::from_bits(16),
            F32 => Size::from_bits(32),
            F64 => Size::from_bits(64),
            F128 => Size::from_bits(128),
        }
    }

    pub fn align<C: HasDataLayout>(self, cx: &C) -> AbiAlign {
        use Float::*;
        let dl = cx.data_layout();
        AbiAlign::new(match self {
            F16 => dl.f16_align,
            F32 => dl.f32_align,
            F64 => dl.f64_align,
            F128 => dl.f128_align,
        })
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash /*Debug*/)]
pub enum Primitive {
    Int(Integer, bool),
    Float(Float),
    Pointer(AddressSpace),
}

impl Primitive {
    // Trusted for the same reason as univariant.rs/values.rs's copy: no
    // trait-level spec on `HasDataLayout::data_layout` for a generic `cx`.
    #[thrust::trusted]
    #[thrust::callable]
    pub fn size<C: HasDataLayout>(self, cx: &C) -> Size {
        use Primitive::*;
        let dl = cx.data_layout();
        match self {
            Int(i, _) => i.size(),
            Float(f) => f.size(),
            Pointer(a) => dl.pointer_size_in(a),
        }
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub fn align<C: HasDataLayout>(self, cx: &C) -> AbiAlign {
        use Primitive::*;
        let dl = cx.data_layout();
        match self {
            Int(i, _) => i.align(dl),
            Float(f) => f.align(dl),
            Pointer(a) => dl.pointer_align_in(a),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct WrappingRange {
    pub start: u128,
    pub end: u128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash /*Debug*/)]
pub enum Scalar {
    Initialized {
        value: Primitive,
        valid_range: WrappingRange,
    },
    Union {
        value: Primitive,
    },
}

impl Scalar {
    pub fn primitive(&self) -> Primitive {
        match *self {
            Scalar::Initialized { value, .. } | Scalar::Union { value } => value,
        }
    }
    pub fn align(self, cx: &impl HasDataLayout) -> AbiAlign {
        self.primitive().align(cx)
    }
    pub fn size(self, cx: &impl HasDataLayout) -> Size {
        self.primitive().size(cx)
    }
}

#[derive(Copy, Clone, /*Debug,*/ PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AddressSpace(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash /*Debug*/)]
pub struct Niche {
    pub offset: Size,
    pub value: Primitive,
    pub valid_range: WrappingRange,
}

impl Niche {
    pub fn from_scalar<C: HasDataLayout>(cx: &C, offset: Size, scalar: Scalar) -> Option<Self> {
        let Scalar::Initialized { value, valid_range } = scalar else {
            return None;
        };
        let niche = Niche {
            offset,
            value,
            valid_range,
        };
        if niche.available(cx) > 0 {
            Some(niche)
        } else {
            None
        }
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub fn available<C: HasDataLayout>(&self, cx: &C) -> u128 {
        let Self {
            value,
            valid_range: v,
            ..
        } = *self;
        let size = value.size(cx);
        assert!(size.bits() <= 128);
        let max_value = size.unsigned_int_max();
        let niche = v.end.wrapping_add(1)..v.start;
        niche.end.wrapping_sub(niche.start) & max_value
    }
}

// //== ./src/lib.rs (verbatim, ReprOptions family)

#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub struct ReprFlags(u8);

impl ReprFlags {
    pub const IS_C: ReprFlags = ReprFlags(1 << 0);
    pub const IS_SIMD: ReprFlags = ReprFlags(1 << 1);
    pub const IS_TRANSPARENT: ReprFlags = ReprFlags(1 << 2);
    pub const IS_LINEAR: ReprFlags = ReprFlags(1 << 3);
    pub const RANDOMIZE_LAYOUT: ReprFlags = ReprFlags(1 << 4);
    pub const PASS_INDIRECTLY_IN_NON_RUSTIC_ABIS: ReprFlags = ReprFlags(1 << 5);
    pub const IS_SCALABLE: ReprFlags = ReprFlags(1 << 6);
    pub const FIELD_ORDER_UNOPTIMIZABLE: ReprFlags = ReprFlags(
        ReprFlags::IS_C.bits()
            | ReprFlags::IS_SIMD.bits()
            | ReprFlags::IS_SCALABLE.bits()
            | ReprFlags::IS_LINEAR.bits(),
    );
    pub const ABI_UNOPTIMIZABLE: ReprFlags =
        ReprFlags(ReprFlags::IS_C.bits() | ReprFlags::IS_SIMD.bits());

    pub const fn bits(&self) -> u8 {
        self.0
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub const fn contains(&self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub const fn intersects(&self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

#[derive(Copy, Clone, /*Debug,*/ Eq, PartialEq)]
pub enum IntegerType {
    Pointer(bool),
    Fixed(Integer, bool),
}

#[derive(Copy, Clone, /*Debug,*/ Eq, PartialEq)]
pub enum ScalableElt {
    ElementCount(u16),
    Container,
}

#[derive(Copy, Clone, /*Debug,*/ Eq, PartialEq, Default)]
pub struct ReprOptions {
    pub int: Option<IntegerType>,
    pub align: Option<Align>,
    pub pack: Option<Align>,
    pub flags: ReprFlags,
    pub scalable: Option<ScalableElt>,
    pub field_shuffle_seed: Hash64,
}

impl ReprOptions {
    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn transparent(&self) -> bool {
        self.flags.contains(ReprFlags::IS_TRANSPARENT)
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub fn inhibit_newtype_abi_optimization(&self) -> bool {
        self.flags.intersects(ReprFlags::ABI_UNOPTIMIZABLE)
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub fn inhibit_struct_field_reordering(&self) -> bool {
        self.flags.intersects(ReprFlags::FIELD_ORDER_UNOPTIMIZABLE) || self.int.is_some()
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub fn can_randomize_type_layout(&self) -> bool {
        !self.inhibit_struct_field_reordering() && self.flags.contains(ReprFlags::RANDOMIZE_LAYOUT)
    }
}

// //== ./src/layout.rs / ./src/layout/coroutine.rs value types (verbatim)

#[derive(PartialEq, Eq, Hash, Clone /*Debug*/)]
pub enum FieldsShape<FieldIdx: Idx> {
    Primitive,
    Union(std::num::NonZeroUsize),
    Array {
        stride: Size,
        count: u64,
    },
    Arbitrary {
        offsets: IndexVec<FieldIdx, Size>,
        in_memory_order: IndexVec<u32, FieldIdx>,
    },
}

// `offsets` and `in_memory_order` are `IndexVec`s, whose model is a sequence, inside a
// `Model = Self` enum, so a formula reaches the sequences through `Seq`'s `PartialEq` with a
// type whose model it is (univariant.rs, where `IndexVec` models as itself, reads `raw`).
#[thrust_macros::context]
impl<FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>> FieldsShape<FieldIdx> {
    /// `self` is `Arbitrary` over `n` fields: `n` offsets, and a memory order listing each
    /// field below `n` exactly once.
    #[thrust_macros::predicate]
    fn arbitrary_of(self, n: Int) -> bool {
        exists(|o: IndexVec<FieldIdx, Size>, m: IndexVec<u32, FieldIdx>,
                os: Seq<Size>, ms: Seq<<FieldIdx as thrust_models::Model>::Ty>|
            self == FieldsShape::Arbitrary { offsets: o, in_memory_order: m }
                && os == o
                && ms == m
                && os.len() == n
                && ms.len() == n
                && forall(|k: Int, i: Int|
                    !(0 <= k && k < n && <FieldIdx as Idx>::index_is(ms[k], i)) || (0 <= i && i < n))
                && forall(|k: Int, k2: Int, i: Int|
                    !(0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2)
                        && <FieldIdx as Idx>::index_is(ms[k], i))
                        || !<FieldIdx as Idx>::index_is(ms[k2], i)))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash /*Debug*/)]
pub struct NumScalableVectors(pub u8);

#[derive(Clone, Copy, PartialEq, Eq, Hash /*Debug*/)]
pub enum BackendRepr {
    Scalar(Scalar),
    ScalarPair(Scalar, Scalar),
    SimdScalableVector {
        element: Scalar,
        count: u64,
        number_of_vectors: NumScalableVectors,
    },
    SimdVector {
        element: Scalar,
        count: u64,
    },
    Memory {
        sized: bool,
    },
}

impl BackendRepr {
    #[inline]
    pub fn is_unsized(&self) -> bool {
        match *self {
            BackendRepr::Scalar(_)
            | BackendRepr::ScalarPair(..)
            | BackendRepr::SimdScalableVector { .. }
            | BackendRepr::SimdVector { .. } => false,
            BackendRepr::Memory { sized } => !sized,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone /*Debug*/)]
pub enum Variants<FieldIdx: Idx, VariantIdx: Idx> {
    Empty,
    Single {
        index: VariantIdx,
    },
    Multiple {
        tag: Scalar,
        tag_encoding: TagEncoding<VariantIdx>,
        tag_field: FieldIdx,
        variants: IndexVec<VariantIdx, VariantLayout<FieldIdx>>,
    },
}

#[derive(PartialEq, Eq, Hash, Copy, Clone /*Debug*/)]
pub enum TagEncoding<VariantIdx: Idx> {
    Direct,
    Niche {
        untagged_variant: VariantIdx,
        niche_variants: RangeInclusive<VariantIdx>,
        niche_start: u128,
    },
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct LayoutData<FieldIdx: Idx, VariantIdx: Idx> {
    pub fields: FieldsShape<FieldIdx>,
    pub variants: Variants<FieldIdx, VariantIdx>,
    pub backend_repr: BackendRepr,
    pub largest_niche: Option<Niche>,
    pub uninhabited: bool,
    pub align: AbiAlign,
    pub size: Size,
    pub max_repr_align: Option<Align>,
    pub unadjusted_abi_align: Align,
    pub randomization_seed: Hash64,
}

impl<FieldIdx: Idx, VariantIdx: Idx> LayoutData<FieldIdx, VariantIdx> {
    pub fn is_uninhabited(&self) -> bool {
        self.uninhabited
    }
}

impl<FieldIdx: Idx, VariantIdx: Idx> LayoutData<FieldIdx, VariantIdx> {
    #[inline]
    pub fn is_unsized(&self) -> bool {
        self.backend_repr.is_unsized()
    }

    pub fn is_zst(&self) -> bool {
        match self.backend_repr {
            BackendRepr::Scalar(_)
            | BackendRepr::ScalarPair(..)
            | BackendRepr::SimdScalableVector { .. }
            | BackendRepr::SimdVector { .. } => false,
            BackendRepr::Memory { sized } => sized && self.size.bytes() == 0,
        }
    }
}

// `PartialEq` added (rewrites.md S10): `univariant`'s requires tests for `MaybeUnsized`.
#[derive(Copy, Clone, PartialEq /*Debug*/)]
pub enum StructKind {
    AlwaysSized,
    MaybeUnsized,
    Prefixed(Size, Align),
}

#[derive(PartialEq, Eq, Hash, Clone /*Debug*/)]
pub struct VariantLayout<FieldIdx: Idx> {
    pub size: Size,
    pub backend_repr: BackendRepr,
    pub field_offsets: IndexVec<FieldIdx, Size>,
    fields_in_memory_order: IndexVec<u32, FieldIdx>,
    largest_niche: Option<Niche>,
    uninhabited: bool,
}

impl<FieldIdx: Idx> VariantLayout<FieldIdx> {
    pub fn from_layout(layout: LayoutData<FieldIdx, impl Idx>) -> Self {
        let FieldsShape::Arbitrary {
            offsets,
            in_memory_order,
        } = layout.fields
        else {
            panic!();
        };
        Self {
            size: layout.size,
            backend_repr: layout.backend_repr,
            field_offsets: offsets,
            fields_in_memory_order: in_memory_order,
            largest_niche: layout.largest_niche,
            uninhabited: layout.uninhabited,
        }
    }

    pub fn is_uninhabited(&self) -> bool {
        self.uninhabited
    }

    pub fn has_fields(&self) -> bool {
        self.field_offsets.len() > 0
    }
}

// //== ./src/layout/simple.rs (verbatim, trusted per the stage plan)

impl<FieldIdx: Idx, VariantIdx: Idx> LayoutData<FieldIdx, VariantIdx> {
    #[thrust::trusted]
    #[thrust::callable]
    pub fn scalar_pair<C: HasDataLayout>(cx: &C, a: Scalar, b: Scalar) -> Self {
        let dl = cx.data_layout();
        let b_align = b.align(dl).abi;
        let align = a.align(dl).abi.max(b_align).max(dl.aggregate_align);
        let b_offset = a.size(dl).align_to(b_align);
        let size = (b_offset + b.size(dl)).align_to(align);
        let largest_niche = Niche::from_scalar(dl, b_offset, b)
            .into_iter()
            .chain(Niche::from_scalar(dl, Size::ZERO, a))
            .max_by_key(|niche| niche.available(dl));
        let combined_seed = a.size(dl).bytes().wrapping_add(b.size(dl).bytes());
        LayoutData {
            variants: Variants::Single {
                index: VariantIdx::new(0),
            },
            fields: FieldsShape::Arbitrary {
                offsets: [Size::ZERO, b_offset].into(),
                in_memory_order: [FieldIdx::new(0), FieldIdx::new(1)].into(),
            },
            backend_repr: BackendRepr::ScalarPair(a, b),
            largest_niche,
            uninhabited: false,
            align: AbiAlign::new(align),
            size,
            max_repr_align: None,
            unadjusted_abi_align: align,
            randomization_seed: Hash64::new(combined_seed),
        }
    }
}

// //== ./src/layout.rs: LayoutCalculator (verbatim; `univariant` /
// `univariant_biased` stay trusted, per the stage plan and univariant.rs)

enum NicheBias {
    Start,
    End,
}

#[derive(Copy, Clone, /*Debug,*/ PartialEq, Eq)]
pub enum LayoutCalculatorError<F> {
    UnexpectedUnsized(F),
    SizeOverflow,
    EmptyUnion,
    ReprConflict,
    ZeroLengthSimdType,
    OversizedSimdType { max_lanes: u64 },
    NonPrimitiveSimdType(F),
}

type LayoutCalculatorResult<FieldIdx, VariantIdx, F> =
    Result<LayoutData<FieldIdx, VariantIdx>, LayoutCalculatorError<F>>;

#[derive(Clone, Copy /*Debug*/)]
pub struct LayoutCalculator<Cx> {
    pub cx: Cx,
}

#[thrust_macros::context]
impl<Cx: HasDataLayout> LayoutCalculator<Cx> {
    // The contract of univariant.rs (stage 6). `requires` is the panic condition of `univariant` and
    // `univariant_biased` apart from the data layout and the field layouts: `fields.indices()`
    // builds every field index up to `fields.len()`, the single variant is `VariantIdx::new(0)`,
    // and `MaybeUnsized` takes `fields.len() - 1`, which wraps below zero (overflow checks are off)
    // so that the slice `[..end]` panics. Not stated: `dl_wf` of the data layout and `niche_wf` of
    // every field's niche, which `Niche::available`, `Primitive::size` and `Size::checked_add`
    // need, and that the `NicheBias::End` layout succeeds and keeps a niche whenever the `Start`
    // one does (the two `unwrap_without_debug`s). The data layout is reached through the generic
    // `Cx::data_layout()`, and `F`'s model is not related to the `LayoutData` it dereferences to,
    // so neither can be named. `ensures`: an `Ok` layout has `Arbitrary` fields over
    // `fields.len()` fields, its memory order a permutation (`FieldsShape::arbitrary_of`).
    #[thrust::trusted]
    #[thrust_macros::requires(
        forall(|k: Int| !(0 <= k && k <= (*fields).len()) || <FieldIdx as Idx>::can_new(k))
            && forall(|z: Int| !(z == 0usize) || <VariantIdx as Idx>::can_new(z))
            && (kind == StructKind::MaybeUnsized ==> (*fields).len() > 0)
    )]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>|
        result != Ok(l) || FieldsShape::<FieldIdx>::arbitrary_of(l.fields, (*fields).len())))]
    pub fn univariant<
        'a,
        FieldIdx: Idx,
        VariantIdx: Idx,
        F: Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        &self,
        fields: &IndexSlice<FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
    ) -> LayoutCalculatorResult<FieldIdx, VariantIdx, F> {
        unimplemented!()
    }
}

trait Unwrap<T> {
    fn unwrap_without_debug(self) -> T;
}

impl<T, E> Unwrap<T> for Result<T, E> {
    fn unwrap_without_debug(self) -> T {
        let Ok(item) = self else {
            panic!();
        };
        item
    }
}

impl<T> Unwrap<T> for Option<T> {
    fn unwrap_without_debug(self) -> T {
        let Some(item) = self else {
            panic!();
        };
        item
    }
}

// //== local to the case study: iterator specs that std.rs does not have yet, and local definitions
// in place of std's `Map`, `Filter`, `extend` and `collect` (rewrites.md R8), verified against the
// contracts written here.

// local to the case study, as in eligibility.rs
#[thrust_macros::context]
impl<'a, T: Idx + thrust_models::Model> IteratorSpec for BitIter<'a, T>
where
    T::Ty: PartialEq,
{
    // The model is (bound, count, left): the column bound of the bit set the iterator walks
    // (`num_columns` of the matrix row, `domain_size` of a `DenseBitSet`), which never changes,
    // the number of items yielded so far, and the number still to yield. Every yielded element
    // is below the bound, and the elements are distinct, so count + left stays at most the bound.
    // `left` makes completion observable: the iterator completes with nothing left, which
    // `Map`'s `reinitialize` in layout.rs needs.
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.1 && 0 <= self.2 && self.1 + self.2 <= self.0
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<T>, o: Self) -> bool {
        self.0 == o.0
            && o.1 == self.1 + visited.len()
            && o.1 <= self.0
            && o.2 + visited.len() == self.2
            && 0 <= o.2
            && forall(|i: Int, k: Int|
                !(0 <= i && i < visited.len() && <T as Idx>::index_is(visited[i], k)) || k < self.0)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).2 == 0 && *self == !self
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

// local to the case study
#[thrust_macros::context]
impl<'a, T: thrust_models::Model> IteratorSpec for SliceIter<'a, T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.1 && self.1 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<&'a T>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == &self.0[self.1 + i])
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

// local to the case study
#[thrust_macros::context]
impl<'a, I: Idx + thrust_models::Model, T: thrust_models::Model> IteratorSpec for IterEnumerated<'a, I, T>
where
    I::Ty: PartialEq,
    T::Ty: PartialEq,
{
    // `next` builds `I::new(pos)`, so the invariant carries `can_new` of the positions left.
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.1 && self.1 <= self.0.len()
            && forall(|k: Int| !(self.1 <= k && k < self.0.len()) || <I as Idx>::can_new(k))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<(I, &'a T)>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i].1 == &self.0[self.1 + i])
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

// local to the case study: `next` of the `Iterator` impl above requires the invariant, as `Map`'s
// below does.
#[thrust_macros::context]
impl<'a, I: Idx + thrust_models::Model, T: thrust_models::Model> IterEnumerated<'a, I, T>
where
    I::Ty: PartialEq,
    T::Ty: PartialEq,
{
    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*it))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!it)
            && (result == None ==> <Self as IteratorSpec>::completed(it))
            && forall(|x: <(I, &'a T) as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as IteratorSpec>::produces(*it, Seq::singleton(x), !it))
    )]
    fn _extern_spec_next(it: &mut IterEnumerated<'a, I, T>) -> Option<(I, &'a T)> {
        <IterEnumerated<'a, I, T> as Iterator>::next(it)
    }
}

// Rewrite (rewrites.md R8): a local `Map` in place of `iter::Map`, evaluation 1's adapter
// (tests/ui/pass/creusot/map.rs) on std.rs's `IteratorSpec`. The model is the inner iterator and
// the closure state; `produces` carries the input items `s` and the chain `fs` of closure states.
struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I: thrust_models::Model, F> thrust_models::Model for Map<I, F> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<F>);
}

// Creusot's `next_precondition`, `preservation_inv`, `reinitialize` and `produces`, and the lemma
// that proves `produces_trans`.
#[thrust_macros::context]
impl<I, B, F> Map<I, F>
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::requires(
        I::inv(iter)
            && Self::reinitialize()
            && Self::preservation_inv(iter, func)
            && Self::next_precondition(iter, func)
    )]
    #[thrust_macros::ensures(result.0 == iter && result.1 == func)]
    fn new(iter: I, func: F) -> Map<I, F> {
        Map { iter, func }
    }

    #[thrust_macros::predicate]
    fn next_precondition(iter: I, func: F) -> bool {
        forall(|e: <I::Item as thrust_models::Model>::Ty| forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
    }

    #[thrust_macros::predicate]
    fn preservation_inv(iter: I, func: F) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e1: <I::Item as thrust_models::Model>::Ty|
        forall(|e2: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
        forall(|f1: Closure<F>|
        forall(|f2: Closure<F>|
        forall(|b: <B as thrust_models::Model>::Ty|
            !(thrust_macros::unnest!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::pre!(f1(e1))
                && thrust_macros::post!(Mut::new(f1, f2)(e1), b))
                || thrust_macros::pre!(f2(e2)))))))))
    }

    #[thrust_macros::predicate]
    fn reinitialize() -> bool {
        forall(|cur: <I as thrust_models::Model>::Ty| forall(|fin: <I as thrust_models::Model>::Ty| forall(|f: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, f)
                    && Self::preservation_inv(fin, f)))))
    }

    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Vec<B>, o: Self, s: Seq<<I::Item as thrust_models::Model>::Ty>, fs: Seq<F>) -> bool {
        thrust_macros::unnest!(s0.1, o.1)
            && s.len() == visited.len()
            && I::produces(s0.0, s, o.0)
            && fs.len() == visited.len() + 1
            && fs[0] == s0.1
            && fs[visited.len()] == o.1
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || (thrust_macros::unnest!(s0.1, fs[k])
                        && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k]), visited[k])))
    }

    // `produces_at` of the joined witnesses: the input items concatenated and the closure states
    // joined at their shared state.
    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
            || Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc)))))))]
    fn produces_trans_at(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as thrust_models::Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as thrust_models::Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }

    // `next` of the `Iterator` impl below, where the ghost snapshots cannot be written (a
    // `context` impl adds `Model` bounds that std's trait does not have): Creusot's contract of
    // `next` on `Map`, the invariant holds before and after.
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*self))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!self)
            && (result == None ==> <Self as IteratorSpec>::completed(self))
            && forall(|x: <B as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as IteratorSpec>::produces(*self, Seq::singleton(x), !self))
    )]
    fn next_map(&mut self) -> Option<B> {
        let pre = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
        let r = self.iter.next();
        match r {
            Some(v) => {
                let e = thrust_macros::ghost!(|v: <I as Iterator>::Item| -> <I as Iterator>::Item { v });
                let b = (self.func)(v);
                let post = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
                let bm = thrust_macros::ghost!(|b: B| -> B { b });
                // Keeps `self` live at the snapshot `post`.
                let _keep = &*self;
                Some(b)
            }
            None => None,
        }
    }

    // The same contract on `Iterator::next`, which `std.rs` gives only for `I: IteratorSpec` with
    // no precondition.
    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*it))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!it)
            && (result == None ==> <Self as IteratorSpec>::completed(it))
            && forall(|x: <B as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as IteratorSpec>::produces(*it, Seq::singleton(x), !it))
    )]
    fn _extern_spec_next(it: &mut Map<I, F>) -> Option<B> {
        <Map<I, F> as Iterator>::next(it)
    }
}

impl<I, B, F> Iterator for Map<I, F>
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    type Item = B;

    fn next(&mut self) -> Option<B> {
        self.next_map()
    }
}

#[thrust_macros::context]
impl<I, B, F> IteratorSpec for Map<I, F>
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        Self::reinitialize()
            && Self::preservation_inv(self.0, self.1)
            && I::inv(self.0)
            && Self::next_precondition(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<B>, o: Self) -> bool {
        thrust_macros::unnest!(self.1, o.1)
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|fs: Seq<Closure<F>>|
                Self::produces_at(self, visited, o, s, fs)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
        let ga = thrust_macros::ghost!(|a: &Self| -> Self { *a });
        let gb = thrust_macros::ghost!(|b: &Self| -> Self { *b });
        let gc = thrust_macros::ghost!(|c: &Self| -> Self { *c });
        let gab = thrust_macros::ghost!(|ab: Seq<<B as thrust_models::Model>::Ty>| -> Seq<<B as thrust_models::Model>::Ty> { ab });
        let gbc = thrust_macros::ghost!(|bc: Seq<<B as thrust_models::Model>::Ty>| -> Seq<<B as thrust_models::Model>::Ty> { bc });
        Self::produces_trans_at(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
    }
}

// Rewrite (rewrites.md R8): a local `Filter` in place of `iter::Filter`, in the form of `Map`
// above, with two of the three restrictions of Creusot's `Filter` (creusot-std/src/std/iter/
// filter.rs): the closure's captures are used immutably (`P: Fn`, so its state never changes),
// and, in place of a closure without a precondition, the precondition holds on every item the
// inner iterator can yield (`pre_all`; rustc's closure in `layout()` can panic). The closure's
// postcondition need not be precise: `produces` states the count only, the items yielded are at
// most the input items the inner iterator produced, and not which of them.
struct Filter<I, P> {
    iter: I,
    predicate: P,
}

impl<I: thrust_models::Model, P> thrust_models::Model for Filter<I, P> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<P>);
}

#[thrust_macros::context]
impl<I, P> Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::requires(
        I::inv(iter)
            && Self::reinitialize()
            && Self::pre_all(iter, predicate)
    )]
    #[thrust_macros::ensures(result.0 == iter && result.1 == predicate)]
    fn new(iter: I, predicate: P) -> Filter<I, P> {
        Filter { iter, predicate }
    }

    // The closure's precondition holds on every item `iter` can yield, after any number of others.
    #[thrust_macros::predicate]
    fn pre_all(iter: I, func: P) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, s.push(e), i) || thrust_macros::pre!(func(&e)))))
    }

    // Creusot's `reinitialize`: after completion, the precondition holds again.
    #[thrust_macros::predicate]
    fn reinitialize() -> bool {
        forall(|cur: <I as thrust_models::Model>::Ty| forall(|fin: <I as thrust_models::Model>::Ty|
            !I::completed(Mut::new(cur, fin))
                || forall(|f: Closure<P>| Self::pre_all(fin, f))))
    }

    // The precondition holds of `Self`'s state.
    #[thrust_macros::predicate]
    fn pre_ok(a: Self) -> bool {
        Self::pre_all(a.0, a.1)
    }

    // `b` follows `a` by yielding `x`, and the closure is the same.
    #[thrust_macros::predicate]
    fn stepped(a: Self, x: I::Item, b: Self) -> bool {
        Self::pre_ok(a) && I::produces(a.0, Seq::singleton(x), b.0) && a.1 == b.1
    }

    // `pre_all` moves along one yielded item; the lemma proves it apart from the loop that uses it.
    #[thrust_macros::requires(Self::stepped(a, x, b))]
    #[thrust_macros::ensures(Self::pre_ok(b))]
    fn pre_all_step(a: Ghost<Self>, x: Ghost<I::Item>, b: Ghost<Self>) {}

    // `produces` with its input items `s` given.
    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Vec<I::Item>, o: Self, s: Seq<<I::Item as thrust_models::Model>::Ty>) -> bool {
        s0.1 == o.1
            && I::produces(s0.0, s, o.0)
            && visited.len() <= s.len()
    }

    // `produces_at` of the joined witnesses.
    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        !(Self::produces_at(a, ab, b, sab) && Self::produces_at(b, bc, c, sbc))
            || Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc)))))]
    fn produces_trans_at(
        a: Ghost<Self>,
        ab: Ghost<Seq<<I::Item as thrust_models::Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<I::Item as thrust_models::Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }

    // `next` of the `Iterator` impl below, where the invariant cannot be written (a `context` impl
    // adds `Model` bounds that std's trait does not have).
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*self))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!self)
            && (result == None ==> <Self as IteratorSpec>::completed(self))
            && forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as IteratorSpec>::produces(*self, Seq::singleton(x), !self))
    )]
    fn next_filter(&mut self) -> Option<I::Item> {
        // `skipped` records the items the closure rejected, for the loop invariant.
        let this = self;
        let mut skipped: Vec<I::Item> = Vec::new();
        loop {
            thrust_macros::invariant!(
                |this: &mut Filter<I, P>, skipped: Vec<I::Item>, self: thrust_models::FnParam<&mut Filter<I, P>>|
                    !this == !self.at_entry()
                        && Filter::<I, P>::reinitialize()
                        && Filter::<I, P>::pre_all((*this).0, (*this).1)
                        && I::inv((*this).0)
                        && (*this).1 == (*self.at_entry()).1
                        && I::produces((*self.at_entry()).0, skipped, (*this).0)
            );
            let before = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
            let Some(x) = this.iter.next() else {
                break;
            };
            let yielded = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
            let after = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
            Filter::<I, P>::pre_all_step(before, yielded, after);
            if (this.predicate)(&x) {
                return Some(x);
            }
            skipped.push(x);
        }
        None
    }

    // The same contract on `Iterator::next`, which `std.rs` gives only for `I: IteratorSpec` with
    // no precondition.
    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*it))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!it)
            && (result == None ==> <Self as IteratorSpec>::completed(it))
            && forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as IteratorSpec>::produces(*it, Seq::singleton(x), !it))
    )]
    fn _extern_spec_next(it: &mut Filter<I, P>) -> Option<I::Item> {
        <Filter<I, P> as Iterator>::next(it)
    }
}

impl<I, P> Iterator for Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        self.next_filter()
    }
}

#[thrust_macros::context]
impl<I, P> IteratorSpec for Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        Self::reinitialize()
            && I::inv(self.0)
            && Self::pre_all(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<I::Item>, o: Self) -> bool {
        exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
            Self::produces_at(self, visited, o, s))
    }

    // The inner iterator produced the rest, then completed.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 == (!self).1
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|mid: <I as thrust_models::Model>::Ty|
                I::produces((*self).0, s, mid)
                    && I::completed(Mut::new(mid, (!self).0))))
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
        let ga = thrust_macros::ghost!(|a: &Self| -> Self { *a });
        let gb = thrust_macros::ghost!(|b: &Self| -> Self { *b });
        let gc = thrust_macros::ghost!(|c: &Self| -> Self { *c });
        let gab = thrust_macros::ghost!(|ab: Seq<<I::Item as thrust_models::Model>::Ty>| -> Seq<<I::Item as thrust_models::Model>::Ty> { ab });
        let gbc = thrust_macros::ghost!(|bc: Seq<<I::Item as thrust_models::Model>::Ty>| -> Seq<<I::Item as thrust_models::Model>::Ty> { bc });
        Self::produces_trans_at(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
    }
}

// Rewrite (rewrites.md R8): `iter_all(it, f)` for `it.all(f)`, with a verified body. Like `all`
// it stops at the first item the closure rejects. `F: Fn` as in `Filter`, the closure's
// precondition must hold on every item the iterator can yield, and the items are `Copy` (the
// site iterates references), so the loop can record what it passed to the closure.
struct IterAllSpec<I, F>(PhantomData<(I, F)>);

#[thrust_macros::context]
impl<I, F> IterAllSpec<I, F>
where
    I: IteratorSpec,
    F: Fn(I::Item) -> bool,
    I::Item: thrust_models::Model + Copy,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn pre_all(iter: I, func: F) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, s.push(e), i) || thrust_macros::pre!(func(e)))))
    }

    // `b` follows `a` by yielding `x`.
    #[thrust_macros::predicate]
    fn stepped(a: I, x: I::Item, b: I, func: F) -> bool {
        Self::pre_all(a, func) && I::produces(a, Seq::singleton(x), b)
    }

    // `pre_all` moves along one yielded item; the lemma is proved apart from the loop.
    #[thrust_macros::requires(Self::stepped(a, x, b, func))]
    #[thrust_macros::ensures(Self::pre_all(b, func))]
    fn pre_all_step(a: Ghost<I>, x: Ghost<I::Item>, b: Ghost<I>, func: Ghost<F>) {}

    #[thrust_macros::predicate]
    fn accepted(func: F, seen: Vec<I::Item>) -> bool {
        forall(|k: Int| !(0 <= k && k < seen.len()) || thrust_macros::post!(func(seen[k]), true))
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(iter) && IterAllSpec::<I, F>::pre_all(iter, f))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<I::Item as thrust_models::Model>::Ty>,
           mid: <I as thrust_models::Model>::Ty|
        I::produces(iter, visited, mid)
            && (result == true ==>
                exists(|fin: <I as thrust_models::Model>::Ty| I::completed(Mut::new(mid, fin)))
                    && forall(|k: Int| !(0 <= k && k < visited.len()) || thrust_macros::post!(f(visited[k]), true)))
            && (result == false ==>
                0 < visited.len()
                    && thrust_macros::post!(f(visited[visited.len() - 1]), false)
                    && forall(|k: Int| !(0 <= k && k < visited.len() - 1) || thrust_macros::post!(f(visited[k]), true))))
)]
fn iter_all<I, F>(iter: I, f: F) -> bool
where
    I: IteratorSpec,
    F: Fn(I::Item) -> bool,
    I::Item: thrust_models::Model + Copy,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    I::produces_refl(&it);
    // `seen` records the items passed to the closure, for the loop invariant.
    let mut seen: Vec<I::Item> = Vec::new();
    loop {
        thrust_macros::invariant!(
            |it: I, seen: Vec<I::Item>, iter: thrust_models::FnParam<I>, f: F|
                I::inv(it)
                    && I::produces(iter.at_entry(), seen, it)
                    && IterAllSpec::<I, F>::accepted(f, seen)
                    && IterAllSpec::<I, F>::pre_all(it, f)
        );
        let before = thrust_macros::ghost!(|it: I| -> I { it });
        let Some(x) = it.next() else {
            return true;
        };
        let yielded = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
        let after = thrust_macros::ghost!(|it: I| -> I { it });
        let fs = thrust_macros::ghost!(|f: F| -> F { f });
        IterAllSpec::<I, F>::pre_all_step(before, yielded, after, fs);
        if !f(x) {
            return false;
        }
        seen.push(x);
    }
}

// Rewrite (rewrites.md R8): `extend` with a verified body, in place of `Extend::extend` (whose
// std body is not analysed): `self` ends as its entry value followed by what `iter` produced
// before it completed.
#[thrust_macros::context]
impl<I: Idx, T: thrust_models::Model + Copy> IndexVec<I, T>
where
    I: thrust_models::Model,
    I::Ty: PartialEq,
    T::Ty: PartialEq,
{
    #[thrust_macros::requires(J::inv(iter))]
    #[thrust_macros::ensures(
        exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
               mid: <J as thrust_models::Model>::Ty,
               fin: <J as thrust_models::Model>::Ty|
            J::produces(iter, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && !self == (*self).concat(visited))
    )]
    fn extend_from<J>(&mut self, iter: J)
    where
        J: IteratorSpec<Item = T>,
        <J as thrust_models::Model>::Ty: PartialEq,
    {
        let this = self;
        let mut it = iter;
        J::produces_refl(&it);
        // `pushed` records what `it` produced, so the invariant needs no existential sequence.
        let mut pushed: Vec<T> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: J, this: &mut IndexVec<I, T>, pushed: Vec<T>, iter: thrust_models::FnParam<J>, self: thrust_models::FnParam<&mut IndexVec<I, T>>|
                    !this == !self.at_entry()
                        && J::inv(it)
                        && J::produces(iter.at_entry(), pushed, it)
                        && *this == (*self.at_entry()).concat(pushed)
            );
            this.raw.push(x);
            pushed.push(x);
        }
    }
}

// Rewrite (rewrites.md R8): `collect` with a verified body, in place of `Iterator::collect` into
// an `IndexVec`: the collection is what the iterator produced before it completed.
#[thrust_macros::context]
#[thrust_macros::requires(J::inv(iter))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
           mid: <J as thrust_models::Model>::Ty,
           fin: <J as thrust_models::Model>::Ty|
        J::produces(iter, visited, mid)
            && J::completed(Mut::new(mid, fin))
            && result == visited)
)]
fn collect_index_vec<I, T, J>(iter: J) -> IndexVec<I, T>
where
    I: Idx + thrust_models::Model,
    I::Ty: PartialEq,
    T: thrust_models::Model,
    T::Ty: PartialEq,
    J: IteratorSpec<Item = T>,
    <J as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    J::produces_refl(&it);
    let mut v: Vec<T> = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: J, v: Vec<T>, iter: thrust_models::FnParam<J>|
                J::inv(it) && J::produces(iter.at_entry(), v, it)
        );
        v.push(x);
    }
    // `IndexVec::from_raw(v)`, written out: its model is the sequence `v`.
    IndexVec {
        raw: v,
        _marker: PhantomData,
    }
}

// Rewrite (rewrites.md R8): `collect` into a `Result` of an `IndexVec`, in place of the
// `FromIterator for Result<V, E>` of std: the first `Err` item is returned; otherwise the
// collection holds the `Ok` payloads of what the iterator produced before it completed.
#[thrust_macros::context]
#[thrust_macros::requires(J::inv(iter))]
#[thrust_macros::ensures(
    forall(|v: <IndexVec<I, T> as thrust_models::Model>::Ty| result != Ok(v)
        || exists(|visited: Seq<<Result<T, E> as thrust_models::Model>::Ty>,
                   mid: <J as thrust_models::Model>::Ty,
                   fin: <J as thrust_models::Model>::Ty|
            J::produces(iter, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && visited.len() == v.len()
                && forall(|k: Int| !(0 <= k && k < v.len()) || visited[k] == Ok(v[k]))))
)]
fn collect_index_vec_result<I, T, E, J>(iter: J) -> Result<IndexVec<I, T>, E>
where
    I: Idx + thrust_models::Model,
    I::Ty: PartialEq,
    T: thrust_models::Model,
    T::Ty: PartialEq,
    E: thrust_models::Model,
    E::Ty: PartialEq,
    J: IteratorSpec<Item = Result<T, E>>,
    <J as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    J::produces_refl(&it);
    let mut v: Vec<T> = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: J, v: Vec<T>, iter: thrust_models::FnParam<J>|
                J::inv(it)
                    && exists(|s: Seq<<Result<T, E> as thrust_models::Model>::Ty>|
                        J::produces(iter.at_entry(), s, it)
                            && s.len() == v.len()
                            && forall(|k: Int| !(0 <= k && k < v.len()) || s[k] == Ok(v[k])))
        );
        match x {
            Ok(y) => v.push(y),
            Err(e) => return Err(e),
        }
    }
    Ok(IndexVec {
        raw: v,
        _marker: PhantomData,
    })
}

// The derived `PartialOrd` and `Ord` of `Size` and `Align` compare the single field, so `max` and
// `min` (used in `layout()`) are specified through the field's order, as std.rs does for the
// integers. `Size` compares `raw: u64`, `Align` compares `pow2: u8`.
#[thrust_macros::context]
impl PartialOrdSpec for Size {
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
        (self.raw < other.raw && ord == Some(std::cmp::Ordering::Less))
            || (self.raw == other.raw && ord == Some(std::cmp::Ordering::Equal))
            || (self.raw > other.raw && ord == Some(std::cmp::Ordering::Greater))
    }

    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    ) {
    }
}

#[thrust_macros::context]
impl PartialOrdSpec for Align {
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
        (self.pow2 < other.pow2 && ord == Some(std::cmp::Ordering::Less))
            || (self.pow2 == other.pow2 && ord == Some(std::cmp::Ordering::Equal))
            || (self.pow2 > other.pow2 && ord == Some(std::cmp::Ordering::Greater))
    }

    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    ) {
    }
}

// //== Thrust model declarations

impl<T> thrust_models::Model for DenseBitSet<T> {
    type Ty = (Int, Seq<Int>, ());
}
impl<'a> thrust_models::Model for WordIter<'a> {
    type Ty = Self;
}
impl<'a, T: Idx> thrust_models::Model for BitIter<'a, T> {
    type Ty = (Int, Int, Int);
}
impl<R: Idx, C: Idx> thrust_models::Model for BitMatrix<R, C> {
    type Ty = Self;
}
impl<I: Idx> thrust_models::Model for IdxRange<I> {
    type Ty = Self;
}
impl<'a, T: thrust_models::Model> thrust_models::Model for SliceIter<'a, T> {
    type Ty = (<&'a [T] as thrust_models::Model>::Ty, Int);
}
impl<'a, I: Idx, T: thrust_models::Model> thrust_models::Model for IterEnumerated<'a, I, T> {
    type Ty = (<&'a [T] as thrust_models::Model>::Ty, Int, ());
}
impl<I: Idx, T: thrust_models::Model> thrust_models::Model for IndexVec<I, T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}
// See eligibility.rs/univariant.rs for why `type Ty = Self` is impossible for
// `IndexSlice` (unsized `raw: [T]`) and why the `[T]` model is reused.
impl<I: Idx, T: thrust_models::Model> thrust_models::Model for IndexSlice<I, T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}
impl<VariantIdx: thrust_models::Model, FieldIdx: thrust_models::Model> thrust_models::Model for SavedLocalEligibility<VariantIdx, FieldIdx> {
    type Ty = SavedLocalEligibility<<VariantIdx as thrust_models::Model>::Ty, <FieldIdx as thrust_models::Model>::Ty>;
}
impl<F: thrust_models::Model> thrust_models::Model for LayoutCalculatorError<F> {
    type Ty = LayoutCalculatorError<<F as thrust_models::Model>::Ty>;
}
impl<Cx> thrust_models::Model for LayoutCalculator<Cx> {
    type Ty = Self;
}
impl thrust_models::Model for NicheBias {
    type Ty = Self;
}
impl thrust_models::Model for Hash64 {
    type Ty = Self;
}
impl thrust_models::Model for ReprFlags {
    type Ty = Self;
}
impl thrust_models::Model for IntegerType {
    type Ty = Self;
}
impl thrust_models::Model for ScalableElt {
    type Ty = Self;
}
impl thrust_models::Model for ReprOptions {
    type Ty = Self;
}
impl thrust_models::Model for PointerSpec {
    type Ty = Self;
}
impl thrust_models::Model for TargetDataLayout {
    type Ty = Self;
}
impl thrust_models::Model for Endian {
    type Ty = Self;
}
impl thrust_models::Model for Size {
    type Ty = Self;
}
impl thrust_models::Model for Align {
    type Ty = Self;
}
impl thrust_models::Model for AbiAlign {
    type Ty = Self;
}
impl thrust_models::Model for Integer {
    type Ty = Self;
}
impl thrust_models::Model for Float {
    type Ty = Self;
}
impl thrust_models::Model for Primitive {
    type Ty = Self;
}
impl thrust_models::Model for WrappingRange {
    type Ty = Self;
}
impl thrust_models::Model for Scalar {
    type Ty = Self;
}
impl<FieldIdx: Idx> thrust_models::Model for FieldsShape<FieldIdx> {
    type Ty = Self;
}
impl thrust_models::Model for AddressSpace {
    type Ty = Self;
}
impl thrust_models::Model for NumScalableVectors {
    type Ty = Self;
}
impl thrust_models::Model for BackendRepr {
    type Ty = Self;
}
impl<FieldIdx: Idx, VariantIdx: Idx> thrust_models::Model for Variants<FieldIdx, VariantIdx> {
    type Ty = Self;
}
impl<VariantIdx: Idx> thrust_models::Model for TagEncoding<VariantIdx> {
    type Ty = Self;
}
impl thrust_models::Model for Niche {
    type Ty = Self;
}
impl<FieldIdx: Idx, VariantIdx: Idx> thrust_models::Model for LayoutData<FieldIdx, VariantIdx> {
    type Ty = Self;
}
impl thrust_models::Model for StructKind {
    type Ty = Self;
}
impl<FieldIdx: Idx> thrust_models::Model for VariantLayout<FieldIdx> {
    type Ty = Self;
}

fn main() {}
