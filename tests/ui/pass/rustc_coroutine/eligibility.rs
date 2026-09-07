//@ignore-on-host: draft, blocked on generic slices and std iterator adapters (see README.md)
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// Extracted from tests/ui/pass/traits/rustc-coroutine.rs (rustc's
// rustc_abi::layout::coroutine::coroutine_saved_local_eligibility, adapted).
// Stage 5 of the rustc_coroutine plan (README.md, "段階 5"). The bit-set /
// `Idx` machinery is copied from the already-annotated tests/ui/pass/
// rustc_coroutine/bitset.rs (same underlying code, stage 3/4) rather than
// re-derived, since its predicates (`mem`, `inserted`, `no_mem`, `index_is`)
// are exactly what the eligibility spec needs to build on. `IndexSlice` /
// `IndexVec` / `SliceIter` / `IterEnumerated` are new here (stage 2/4, not
// yet in bitset.rs) and carry a best-effort `Model` for `IndexSlice`: see the
// comment on that `impl` below for why plain `type Ty = Self` cannot work
// and what is chosen instead. This file is a DRAFT: it is not expected to
// verify (`ignore-on-host` above), only to compile and to record where the
// spec is uncertain (`// TODO(spec):`).

use thrust_models::forall;
use thrust_models::model::Int;

use std::fmt::Debug;
use std::hash::Hash;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::slice::SliceIndex;

// //== ./../rustc_index/src/bit_set.rs (verbatim from bitset.rs, stage 3/4)

type Word = u64;
const WORD_BYTES: usize = size_of::<Word>();
const WORD_BITS: usize = WORD_BYTES * 8;

#[derive(/* Eq, PartialEq, */ Hash)]
pub struct DenseBitSet<T> {
    domain_size: usize,
    words: Vec<Word>,
    marker: PhantomData<T>,
}

#[thrust_macros::context]
impl<T: Idx> DenseBitSet<T> {
    /// `i` is a member of the set. The words are a `Vec<u64>` and bit tests
    /// have no model, so membership is read off the word array as "the word
    /// stored at index `i` is non-zero"; every body below is trusted, so this
    /// is just a fixed abstraction function for the set specs.
    #[thrust_macros::predicate]
    fn mem(self, i: usize) -> bool {
        // self.words.array[i] != 0
        "(not (= (select
                    (tuple_proj<Array<Int-Int>-Int>.0
                        (tuple_proj<Int-Tuple<Array<Int-Int>-Int>-Tuple>.1 self_))
                    i)
                 0))";
        true
    }

    /// `dist` is `self` with `i` inserted: same domain, and the word array
    /// updated at `i` only. Phrased on the word array so that the frame
    /// ("every other element keeps its membership") is a select-over-store
    /// for the solver instead of a nested quantifier.
    #[thrust_macros::predicate]
    fn inserted(self, i: usize, dist: Self) -> bool {
        // dist.domain_size == self.domain_size
        //     && dist.words.array == self.words.array.store(i, 1)
        "(and
            (= (tuple_proj<Int-Tuple<Array<Int-Int>-Int>-Tuple>.0 dist)
               (tuple_proj<Int-Tuple<Array<Int-Int>-Int>-Tuple>.0 self_))
            (= (tuple_proj<Array<Int-Int>-Int>.0
                    (tuple_proj<Int-Tuple<Array<Int-Int>-Int>-Tuple>.1 dist))
               (store (tuple_proj<Array<Int-Int>-Int>.0
                          (tuple_proj<Int-Tuple<Array<Int-Int>-Int>-Tuple>.1 self_))
                      i 1)))";
        true
    }

    /// `forall i: !Self::mem(self, i)`, written as one array equality instead
    /// of a quantifier: an unguarded `forall` in the postcondition of a trusted
    /// function becomes a universally quantified *assumption*, and pcsat then
    /// answers `unknown` / times out on the failing twin (see the report).
    #[thrust_macros::predicate]
    fn no_mem(self) -> bool {
        "(= (tuple_proj<Array<Int-Int>-Int>.0
                (tuple_proj<Int-Tuple<Array<Int-Int>-Int>-Tuple>.1 self_))
            ((as const (Array Int Int)) 0))";
        true
    }

    // New for this stage: "l is the k-th element yielded by `self.iter()`".
    // TODO(spec): uninterpreted placeholder. A real definition needs a model
    // of `BitIter`'s traversal order tied to `mem` (e.g. `elem_at(self, k, l)
    // ==> mem(self, l)`, injectivity in `k`, and the count of `k`s below
    // `self.domain_size` equalling `self.count()`); that model is out of
    // scope for this draft (bit-set specs stay set-abstraction only, per the
    // stage plan), so this predicate is left axiom-free (`true`) and every
    // ensures clause that uses it below is marked accordingly.
    #[thrust_macros::predicate]
    fn elem_at(self, k: usize, l: T) -> bool {
        "true";
        true
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::ensures(result.domain_size == domain_size)]
    #[thrust_macros::ensures(Self::no_mem(result))]
    pub fn new_empty(domain_size: usize) -> DenseBitSet<T> {
        let num_words = num_words(domain_size);
        DenseBitSet {
            domain_size,
            words: vec![0; num_words],
            marker: PhantomData,
        }
    }

    #[thrust::trusted]
    #[thrust::callable]
    fn clear_excess_bits(&mut self) {
        clear_excess_bits_in_final_word(self.domain_size, &mut self.words);
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub fn count(&self) -> usize {
        count_ones(&self.words)
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(forall(|i: Int| <T as Idx>::index_is(elem, i) ==> i < (*self).domain_size))]
    #[thrust_macros::ensures(forall(|i: Int| <T as Idx>::index_is(elem, i) && (result == true) ==> Self::mem(*self, i)))]
    #[thrust_macros::ensures(forall(|i: Int| <T as Idx>::index_is(elem, i) && Self::mem(*self, i) ==> (result == true)))]
    pub fn contains(&self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let (word_index, mask) = word_index_and_mask(elem);
        (self.words[word_index] & mask) != 0
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(forall(|i: Int| <T as Idx>::index_is(elem, i) ==> i < (*self).domain_size))]
    #[thrust_macros::ensures((!self).domain_size == (*self).domain_size)]
    #[thrust_macros::ensures(forall(|i: Int| <T as Idx>::index_is(elem, i)
        ==> Self::inserted(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i: Int| <T as Idx>::index_is(elem, i) && (result == true) ==> !Self::mem(*self, i)))]
    #[thrust_macros::ensures(forall(|i: Int| <T as Idx>::index_is(elem, i) && Self::mem(*self, i) ==> (result == false)))]
    pub fn insert(&mut self, elem: T) -> bool {
        assert!(
            elem.index() < self.domain_size,
            "inserting element at index {} but domain size is {}",
            elem.index(),
            self.domain_size,
        );
        let (word_index, mask) = word_index_and_mask(elem);
        let word_ref = &mut self.words[word_index];
        let word = *word_ref;
        let new_word = word | mask;
        *word_ref = new_word;
        new_word != word
    }

    #[thrust::trusted]
    #[thrust_macros::ensures((!self).domain_size == (*self).domain_size)]
    #[thrust_macros::ensures(forall(|i: Int| i < (*self).domain_size ==> Self::mem(!self, i)))]
    pub fn insert_all(&mut self) {
        self.words.fill(!0);
        self.clear_excess_bits();
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn iter(&self) -> BitIter<'_, T> {
        BitIter::new(&self.words)
    }
}

/// Own iterator standing in for `slice::Iter<'a, Word>` (whose raw pointer
/// fields have no model in Thrust): yields `&words[0]`, ..., `&words[len - 1]`.
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
    #[inline]
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
    #[thrust::trusted]
    #[thrust_macros::ensures(result.start == 0)]
    #[thrust_macros::ensures(result.end == (*self).num_rows)]
    pub fn rows(&self) -> IdxRange<R> {
        IdxRange::new(0, self.num_rows)
    }

    #[thrust::trusted]
    #[thrust::callable]
    fn range(&self, row: R) -> (usize, usize) {
        let words_per_row = num_words(self.num_columns);
        let start = row.index() * words_per_row;
        (start, start + words_per_row)
    }

    #[thrust::trusted]
    #[thrust_macros::requires(forall(|i: Int| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    pub fn iter(&self, row: R) -> BitIter<'_, C> {
        assert!(row.index() < self.num_rows);
        let (start, end) = self.range(row);
        BitIter::new(&self.words[start..end])
    }

    #[thrust::trusted]
    #[thrust::callable]
    pub fn count(&self, row: R) -> usize {
        let (start, end) = self.range(row);
        count_ones(&self.words[start..end])
    }
}

#[inline]
#[thrust::trusted]
#[thrust::callable]
fn num_words<T: Idx>(domain_size: T) -> usize {
    domain_size.index().div_ceil(WORD_BITS)
}

#[inline]
#[thrust::trusted]
#[thrust::callable]
fn word_index_and_mask<T: Idx>(elem: T) -> (usize, Word) {
    let elem = elem.index();
    let word_index = elem / WORD_BITS;
    let mask = 1 << (elem % WORD_BITS);
    (word_index, mask)
}

#[thrust::trusted]
#[thrust::callable]
fn clear_excess_bits_in_final_word(domain_size: usize, words: &mut [Word]) {
    let num_bits_in_final_word = domain_size % WORD_BITS;
    if num_bits_in_final_word > 0 {
        let mask = (1 << num_bits_in_final_word) - 1;
        words[words.len() - 1] &= mask;
    }
}

#[inline]
#[thrust::trusted]
#[thrust::callable]
fn count_ones(words: &[Word]) -> usize {
    words.iter().map(|word| word.count_ones() as usize).sum()
}

// //== ./../rustc_index/src/idx.rs (verbatim from bitset.rs, stage 3/4, plus
// `can_new` added here for stage 5's `IndexVec::from_elem_n` / `FieldIdx::new`
// preconditions)

#[thrust_macros::context]
pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    /// `i` is the `usize` index of this element.
    #[thrust_macros::predicate]
    fn index_is(self, i: usize) -> bool;

    /// Precondition of `Self::new(idx)`. `usize`'s impl is unconditionally
    /// true; the eligibility spec only ever instantiates `Idx` with `usize`-
    /// like index types here (the `u32` impl uses an `as` cast Thrust does
    /// not support yet, see the target file's header and the report).
    #[thrust_macros::predicate]
    fn can_new(idx: usize) -> bool;

    fn new(idx: usize) -> Self;

    #[thrust_macros::ensures(Self::index_is(self, result))]
    fn index(self) -> usize;

    #[inline]
    fn increment_by(&mut self, amount: usize) {
        *self = self.plus(amount);
    }

    #[inline]
    #[must_use = "Use `increment_by` if you wanted to update the index in-place"]
    fn plus(self, amount: usize) -> Self {
        Self::new(self.index() + amount)
    }
}

#[thrust_macros::context]
impl Idx for usize {
    #[thrust_macros::predicate]
    fn index_is(self, i: usize) -> bool {
        // i == self
        "(= i self_)";
        true
    }

    #[thrust_macros::predicate]
    fn can_new(idx: usize) -> bool {
        "true";
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

/// Own iterator standing in for `(start..end).map(I::new)`: yields
/// `I::new(start)`, `I::new(start + 1)`, ..., `I::new(end - 1)`.
pub struct IdxRange<I: Idx> {
    start: usize,
    end: usize,
    marker: PhantomData<I>,
}

impl<I: Idx> IdxRange<I> {
    #[thrust::trusted]
    #[thrust::callable]
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

    #[thrust::trusted]
    #[thrust::callable]
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

pub trait IntoSliceIdx<I, T: ?Sized> {
    type Output: SliceIndex<T>;
    fn into_slice_idx(self) -> Self::Output;
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for I {
    type Output = usize;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        self.index()
    }
}

// //== ./../rustc_index/src/slice.rs (new for this stage)

#[derive(PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexSlice<I: Idx, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: [T],
}

/// Own iterator standing in for `slice::Iter<'a, T>` (whose raw pointer
/// fields have no model in Thrust): yields `&raw[0]`, ..., `&raw[len - 1]`.
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

/// Own iterator standing in for
/// `raw.iter().enumerate().map(|(n, t)| (I::new(n), t))`: yields
/// `(I::new(0), &raw[0])`, ..., `(I::new(len - 1), &raw[len - 1])`.
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

impl<I: Idx, T> IndexSlice<I, T> {
    #[inline]
    pub const fn from_raw(raw: &[T]) -> &Self {
        let ptr: *const [T] = raw;

        unsafe { &*(ptr as *const Self) }
    }

    #[inline]
    pub fn from_raw_mut(raw: &mut [T]) -> &mut Self {
        let ptr: *mut [T] = raw;

        unsafe { &mut *(ptr as *mut Self) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.raw.len()
    }

    #[inline]
    pub fn next_index(&self) -> I {
        I::new(self.len())
    }

    #[inline]
    pub fn iter(&self) -> SliceIter<'_, T> {
        SliceIter {
            raw: &self.raw,
            pos: 0,
        }
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
    pub fn indices(&self) -> IdxRange<I> {
        let _ = I::new(self.len());
        IdxRange::new(0, self.len())
    }
}

impl<I: Idx, J: Idx> IndexSlice<I, J> {
    pub fn invert_bijective_mapping(&self) -> IndexVec<J, I> {
        debug_assert_eq!(
            self.iter().map(|x| x.index() as u128).sum::<u128>(),
            (0..self.len() as u128).sum::<u128>(),
        );

        let mut inverse = IndexVec::from_elem_n(Idx::new(0), self.len());
        let mut entries = self.iter_enumerated();
        while let Some((i1, &i2)) = entries.next() {
            inverse[i2] = i1;
        }

        debug_assert_eq!(
            inverse.iter().map(|x| x.index() as u128).sum::<u128>(),
            (0..inverse.len() as u128).sum::<u128>(),
        );

        inverse
    }
}

impl<I: Idx, T, R: IntoSliceIdx<I, [T]>> std::ops::Index<R> for IndexSlice<I, T> {
    type Output = <R::Output as SliceIndex<[T]>>::Output;

    #[inline]
    fn index(&self, index: R) -> &Self::Output {
        &self.raw[index.into_slice_idx()]
    }
}

impl<I: Idx, T, R: IntoSliceIdx<I, [T]>> std::ops::IndexMut<R> for IndexSlice<I, T> {
    #[inline]
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        &mut self.raw[index.into_slice_idx()]
    }
}

// //== ./../rustc_index/src/vec.rs (new for this stage)

use std::borrow::{Borrow, BorrowMut};
use std::ops::{Deref, DerefMut};
use std::{slice, vec};

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

    // Stage 5 needs this: `IndexVec::from_elem_n(Unassigned, nb_locals)` gives
    // an `assignments` vector of exactly `nb_locals` entries, all `Unassigned`.
    #[inline]
    #[thrust_macros::ensures(result.raw.len() == n)]
    // TODO(spec): the intended second clause, `forall i < n: result.raw[i] ==
    // elem`, does not typecheck generically: `elem`'s top-level parameter
    // type is lowered to `<T as Model>::Ty` (per `lower_params`) but
    // `result.raw[i]` (real `Vec` indexing) yields the real, un-lowered `T`,
    // and nothing constrains `T: PartialEq<<T as Model>::Ty>` generically.
    // Dropped for this draft; the only property `coroutine_saved_local_
    // eligibility`'s proof actually needs from `from_elem_n` is the length.
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

impl<I: Idx, T> IndexSlice<I, T> {
    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.raw.iter_mut()
    }
}

// //== ./src/layout/coroutine.rs

#[derive(Clone, Debug, PartialEq)]
enum SavedLocalEligibility<VariantIdx, FieldIdx> {
    Unassigned,
    Assigned(VariantIdx),
    Ineligible(Option<FieldIdx>),
}

// //== Thrust model declarations
//
// `IndexVec`'s model is the struct itself (field-by-field), so `.raw` reaches
// the underlying `Vec<T>` (which in turn has the built-in `Vec` model:
// `.raw.length` / `.raw.array[i]`, as used above and in values.rs / bitset.rs).
impl<I: Idx, T> thrust_models::Model for IndexVec<I, T> {
    type Ty = Self;
}

// `IndexSlice<I, T>` cannot get `type Ty = Self`: its `raw: [T]` field makes
// `IndexSlice` itself unsized, and `Model::Ty` carries an implicit `Sized`
// bound (confirmed with a standalone rustc probe: `type Ty = Self` on an
// unsized `Self` is a hard `error[E0277]`, independent of Thrust). Since
// `coroutine_saved_local_eligibility` takes `&IndexSlice<..>` as a top-level
// parameter, *some* `Model` impl is mandatory too: `FormulaFnTypeLowering::
// lower_params` (thrust-macros/src/formula_fn_type_lowering.rs:56-63)
// unconditionally rewrites every parameter's type to `<T as Model>::Ty`, and
// that projection must resolve for the companion function's signature to be
// well-formed at all, even if the formula body never mentions the parameter.
// The choice here mirrors the built-in `impl<T> Model for [T] where T: Model
// { type Ty = Seq<T::Ty>; }` (std.rs) that `IndexSlice`'s own `raw` field
// already gets: model `IndexSlice<I, T>` the same way its slice models
// itself, dropping the phantom `I` marker (it carries no runtime state).
// TODO(spec): this is untested against Thrust's own analysis passes for a
// *generic* element type T (the target file's header lists generic `[T]` as
// unsupported "in order of appearance" ahead of everything in this file);
// expect this to be exactly where the draft's compile check stops being
// clean, if anywhere. See the report for what actually happened.
impl<I: Idx, T: thrust_models::Model> thrust_models::Model for IndexSlice<I, T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}

impl<'a, T> thrust_models::Model for SliceIter<'a, T> {
    type Ty = Self;
}
impl<'a, I: Idx, T> thrust_models::Model for IterEnumerated<'a, I, T> {
    type Ty = Self;
}
impl<VariantIdx, FieldIdx> thrust_models::Model for SavedLocalEligibility<VariantIdx, FieldIdx> {
    type Ty = Self;
}
impl<T> thrust_models::Model for DenseBitSet<T> {
    type Ty = Self;
}
impl<'a> thrust_models::Model for WordIter<'a> {
    type Ty = Self;
}
impl<'a, T: Idx> thrust_models::Model for BitIter<'a, T> {
    type Ty = Self;
}
impl<R: Idx, C: Idx> thrust_models::Model for BitMatrix<R, C> {
    type Ty = Self;
}
impl<I: Idx> thrust_models::Model for IdxRange<I> {
    type Ty = Self;
}

// //== stage 5 spec: `coroutine_saved_local_eligibility` (README.md, 段階 5)
//
// Notation below follows the README: `a = result.1` (the `assignments`
// vector) and `inel = result.0` (the `ineligible_locals` set).
//
// TODO(spec): the four `ensures` clauses are a direct transcription of the
// README's four bullets; property 3/4 lean on the freshly-introduced
// `DenseBitSet::elem_at` predicate, which is uninterpreted (see its
// definition above) — so as written these two clauses are close to vacuous
// (anything satisfies an implication whose antecedent can't be discharged
// against an axiom-free predicate), which is expected for a draft.
// NOTE: quantifiers below use `usize`, not `Int`: unlike a `predicate` body
// (see `DenseBitSet::mem` etc., which get special HIR-level field-projection
// handling per `analyze::local_def::define_as_predicate` and can use the
// `.length`/`.array[i]` sugar on a real `Vec` field, as in values.rs's
// `dl_wf`), a `requires`/`ensures` body is compiled as an ordinary function
// (`thrust-macros/src/spec.rs`'s `requires_fn`/`ensures_fn`) and really does
// need literal, valid Rust: real `.len()` / real `[usize]` indexing on a
// plain `Vec<T>` field (confirmed empirically: `.raw.array[i]`/`.raw.length`
// on an `IndexVec`'s real `Vec` field is `error[E0609]`, no such field).
// `IndexSlice`'s own model (`Seq`, see the `impl Model for IndexSlice` above)
// *does* have real `.array`/`.length` fields, so those two are kept as-is.
#[thrust_macros::requires(
    forall(|v: usize, f: usize|
        !(0 <= v && v < (*variant_fields).length
            && 0 <= f && f < (*variant_fields).array[v].raw.len())
        || (*variant_fields).array[v].raw[f].index() < nb_locals)
    && (*storage_conflicts).num_rows == nb_locals
    && (*storage_conflicts).num_columns == nb_locals
    && forall(|n: Int| !(0 <= n && n <= nb_locals) || FieldIdx::can_new(n))
    && forall(|v: Int| !(0 <= v && v < (*variant_fields).length) || VariantIdx::can_new(v))
)]
#[thrust_macros::ensures(
    // 1. Unassigned locals never appear in any variant's field list.
    forall(|l: usize| !(0 <= l && l < nb_locals && result.1.raw[l] == SavedLocalEligibility::Unassigned)
        || forall(|v: usize, f: usize|
            !(0 <= v && v < (*variant_fields).length
                && 0 <= f && f < (*variant_fields).array[v].raw.len())
            || !((*variant_fields).array[v].raw[f].index() == l)))
    // 2. Assigned(v) locals appear only under variant v, and only there.
    // TODO(spec): "exists f: variant_fields[v][f] == l" and the "not under
    // any other assigned variant" half are folded into one nested forall/
    // exists below; the exact quantifier shape is a best effort, not
    // checked against the solver (this file does not verify, see header).
    && forall(|l: usize, v: usize|
        !(0 <= l && l < nb_locals
            && result.1.raw[l] == SavedLocalEligibility::Assigned(VariantIdx::new(v)))
        || (v < (*variant_fields).length
            && thrust_models::exists(|f: usize|
                0 <= f && f < (*variant_fields).array[v].raw.len()
                    && (*variant_fields).array[v].raw[f].index() == l)))
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
            || thrust_models::exists(|x: Option<FieldIdx>| result.1.raw[l] == SavedLocalEligibility::Ineligible(x))))
    && forall(|l: usize| !(0 <= l && l < nb_locals) ||
        (!thrust_models::exists(|x: Option<FieldIdx>| result.1.raw[l] == SavedLocalEligibility::Ineligible(x))
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
    use SavedLocalEligibility::*;

    let mut assignments: IndexVec<LocalIdx, _> = IndexVec::from_elem_n(Unassigned, nb_locals);

    let mut ineligible_locals = DenseBitSet::new_empty(nb_locals);

    let mut variants = variant_fields.iter_enumerated();
    while let Some((variant_index, fields)) = variants.next() {
        // TODO(spec): "処理済み variant (0..variant_index) の local は
        // Unassigned でなく、Assigned(v) なら v < variant_index" per the
        // README; written informally here (draft, not expected to verify).
        thrust_macros::invariant!(
            |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>|
            true
        );
        let mut locals = fields.into_iter();
        while let Some(local) = locals.next() {
            thrust_macros::invariant!(|assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>| true);
            match assignments[*local] {
                Unassigned => {
                    assignments[*local] = Assigned(variant_index);
                }
                Assigned(idx) => {
                    ineligible_locals.insert(*local);
                    assignments[*local] = Ineligible(None);
                }
                Ineligible(_) => {}
            }
        }
    }

    let mut rows = storage_conflicts.rows();
    while let Some(local_a) = rows.next() {
        // TODO(spec): conflict loop invariant from the README ("Assigned ->
        // Ineligible transitions only; properties 1, 2's negative half and 4
        // preserved") is not encoded; left `true` for this draft.
        thrust_macros::invariant!(|assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>| true);
        let conflicts_a = storage_conflicts.count(local_a);
        if ineligible_locals.contains(local_a) {
            continue;
        }

        let mut conflicts = storage_conflicts.iter(local_a);
        while let Some(local_b) = conflicts.next() {
            thrust_macros::invariant!(|assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>| true);
            if ineligible_locals.contains(local_b) || assignments[local_a] == assignments[local_b] {
                continue;
            }

            let conflicts_b = storage_conflicts.count(local_b);
            let (remove, other) = if conflicts_a > conflicts_b {
                (local_a, local_b)
            } else {
                (local_b, local_a)
            };
            ineligible_locals.insert(remove);
            assignments[remove] = Ineligible(None);
        }
    }

    {
        let mut used_variants = DenseBitSet::new_empty(variant_fields.len());
        let mut assignments_iter = (&assignments).into_iter();
        while let Some(assignment) = assignments_iter.next() {
            // TODO(spec): "properties 1, 2, 4 preserved" from the README not
            // encoded; `used_variants` itself carries no property needed for
            // panic safety (only `count()` is read below).
            thrust_macros::invariant!(|used_variants: DenseBitSet<VariantIdx>| true);
            if let Assigned(idx) = assignment {
                used_variants.insert(*idx);
            }
        }
        if used_variants.count() < 2 {
            let mut assignments_iter_mut = assignments.iter_mut();
            while let Some(assignment) = assignments_iter_mut.next() {
                *assignment = Ineligible(None);
            }
            ineligible_locals.insert_all();
        }
    }

    {
        let mut ineligible = ineligible_locals.iter().enumerate();
        while let Some((idx, local)) = ineligible.next() {
            // TODO(spec): `idx` is the enumeration position and `local` is
            // the `idx`-th element of `ineligible_locals` in iteration order
            // (`DenseBitSet::elem_at(ineligible_locals, idx, local)`, per the
            // README); not encoded as an invariant here (the underlying
            // `.enumerate()` is a std adapter over our own `BitIter`, itself
            // one of the blocked std-iterator-adapter constructs, see the
            // report).
            thrust_macros::invariant!(|assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>| true);
            assignments[local] = Ineligible(Some(FieldIdx::new(idx)));
        }
    }

    (ineligible_locals, assignments)
}

fn main() {}
