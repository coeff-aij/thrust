//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// Extracted from tests/ui/pass/traits/rustc-coroutine.rs (rustc's
// rustc_index::bit_set and rustc_index::idx, adapted).

use thrust_models::forall;
use thrust_models::model::Int;

use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

// //== ./../rustc_index/src/bit_set.rs

type Word = u64;
const WORD_BYTES: usize = size_of::<Word>();
const WORD_BITS: usize = WORD_BYTES * 8;

// #[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
// `Eq, PartialEq` commented out: the derived `PartialEq` compares the
// `PhantomData` field, whose model is the unit sort, and Thrust panics with
// `unbound var $0` (src/chc/clause_builder.rs:113).
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
    // `Self::inserted` gives, for `i` the index of `elem`:
    //   `Self::mem(!self, i)`, and
    //   `forall j != i: Self::mem(!self, j) <==> Self::mem(*self, j)`.
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

    // A deterministic enumeration spec (`elems(set, seq, n)` plus a `next`
    // that returns `seq[k]` on its k-th call) would need `next` to know which
    // bit it is at; only the weaker index bound below is stated, on
    // `BitIter::next` itself.
    #[inline]
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

// The bit bound below has to be written in raw SMT-LIB2: `self.iter.words`
// has the slice type `&'a [Word]`, and both `BitIter` and `WordIter` model as
// themselves, so in a `requires`/`ensures` -- compiled as an ordinary Rust
// function -- the field keeps that Rust type and the `Seq` accessors are
// rejected (`error[E0609]: no field `length` on type `[u64]``, likewise
// `array`), while `.len()` reaches
// `not implemented: unsupported method call in formula: ... len#0`
// (src/analyze/annot_fn.rs:915). A `predicate` body must be a raw string
// literal anyway, so these project the model tuples by hand:
// `BitIter = (word, offset, iter, marker)` and `WordIter = (words, pos)`,
// with `words = (array, length)`.
#[thrust_macros::context]
impl<'a, T: Idx> BitIter<'a, T> {
    /// `n == self.iter.words.length * WORD_BITS`: the number of bits the
    /// underlying word array holds. Every index this iterator yields is
    /// `bit_pos + offset` for some bit of some word of that array, so this is
    /// a bound on it -- an abstraction, since `next`'s body is trusted and
    /// the wrapping `offset` arithmetic is not modelled.
    #[thrust_macros::predicate]
    fn bit_bound(self, n: usize) -> bool {
        "(= n (* 64 (tuple_proj<Array<Int-Int>-Int>.1 (tuple_proj<Tuple<Array<Int-Int>-Int>-Int>.0 (tuple_proj<Int-Int-Tuple<Tuple<Array<Int-Int>-Int>-Int>-Tuple>.2 self_)))))";
        true
    }

    /// `dist.iter.words == self.iter.words`: `next` never replaces the word
    /// array, so the bound above survives a call.
    #[thrust_macros::predicate]
    fn same_words(self, dist: Self) -> bool {
        "(= (tuple_proj<Tuple<Array<Int-Int>-Int>-Int>.0 (tuple_proj<Int-Int-Tuple<Tuple<Array<Int-Int>-Int>-Int>-Tuple>.2 dist)) (tuple_proj<Tuple<Array<Int-Int>-Int>-Int>.0 (tuple_proj<Int-Int-Tuple<Tuple<Array<Int-Int>-Int>-Int>-Tuple>.2 self_)))";
        true
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    // `WORD_BITS` (a named `const`) is not usable in a formula:
    // `not implemented: unsupported path in formula: ... Def(Const, ..
    // WORD_BITS)` (src/analyze/annot_fn.rs:809), so the literal 64 is used
    // here and in `bit_bound`'s SMT body.
    #[thrust_macros::ensures(Self::bit_bound(result, (*words).length * 64))]
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
    #[thrust::ignored]
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

// `next` implements the real `std::iter::Iterator`, so its spec cannot be
// attached to the impl method: `requires`/`ensures` expand into companion
// items next to the method, and in an `impl Trait for Ty` every item must be
// a trait member (`error[E0407]: method `_thrust_requires_next` is not a
// member of trait `Iterator``). The spec goes on a sibling *inherent* impl as
// an `#[thrust::extern_spec_fn]` wrapper tail-calling the impl method; Thrust
// registers the contract under the impl method's `DefId` and uses it at
// static call sites (see
// tests/ui/pass/rustc_coroutine/notes/foreign_trait_impl_specs.md). The body
// keeps its own `#[thrust::trusted]`, so the contract is assumed, not proved.
#[thrust_macros::context]
impl<'a, T: Idx> BitIter<'a, T> {
    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::same_words(*it, !it))]
    // The weak, safe form: *any* yielded element's index is below the bound.
    // Written as one universal over the payload rather than
    // `result == None || exists(|e| result == Some(e) && ..)`: with the
    // existential, pcsat answers `unknown` on the failing twin instead of
    // `Unsat`.
    #[thrust_macros::ensures(forall(|n: Int, e: <T as thrust_models::Model>::Ty, i: Int|
        Self::bit_bound(*it, n) && result == Some(e) && <T as Idx>::index_is(e, i)
            ==> i < n))]
    fn _extern_spec_next(it: &mut BitIter<'a, T>) -> Option<T>
    where
        T: thrust_models::Model,
        <T as thrust_models::Model>::Ty: PartialEq,
    {
        <BitIter<'a, T> as Iterator>::next(it)
    }
}

// #[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
// `Clone, Eq, PartialEq` commented out: same `PhantomData` ICE as above.
#[derive(/* Clone, Eq, PartialEq, */ Hash)]
pub struct BitMatrix<R: Idx, C: Idx> {
    num_rows: usize,
    num_columns: usize,
    words: Vec<Word>,
    marker: PhantomData<(R, C)>,
}

#[thrust_macros::context]
impl<R: Idx, C: Idx> BitMatrix<R, C> {
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

    // `every yielded C satisfies c.index() < self.num_columns` is still not
    // stated here: `BitIter::next`'s contract bounds the yielded index by the
    // *word array* size (`BitIter::bit_bound`), and relating that to
    // `num_columns` needs `range`/`num_words`, both trusted and unspecified.
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

// //== ./../rustc_index/src/idx.rs

#[thrust_macros::context]
pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    /// `i` is the `usize` index of this element.
    #[thrust_macros::predicate]
    fn index_is(self, i: usize) -> bool;

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
// `Clone` commented out: same `PhantomData` ICE as above.
// #[derive(Clone)]
pub struct IdxRange<I: Idx> {
    start: usize,
    end: usize,
    marker: PhantomData<I>,
}

#[thrust_macros::context]
impl<I: Idx> IdxRange<I> {
    #[thrust_macros::ensures(result.start == start)]
    #[thrust_macros::ensures(result.end == end)]
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

fn main() {
    let mut set: DenseBitSet<usize> = DenseBitSet::new_empty(5);
    set.insert(3);
    assert!(set.contains(3));
    assert!(!set.contains(2));

    // `DenseBitSet::new_empty` says nothing about the length of its word
    // array, so the bound is exercised on an iterator built over a word slice
    // of known length: `BitIter::new`'s ensures turns that into
    // `bit_bound(it, 2 * WORD_BITS)`, `next`'s ensures bounds every yielded
    // index by it, and `same_words` carries the bound to the second call.
    let mut it: BitIter<'static, usize> = BitIter::new(words());
    match it.next() {
        // Broken narrowly: `BitIter::next`'s contract bounds the yielded
        // index by `words.length * 64 == 128`, not by 127.
        Some(e) => assert!(e.index() < 127),
        None => {}
    }
    match it.next() {
        Some(e) => assert!(e.index() < 128),
        None => {}
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((*result).length == 2)]
fn words() -> &'static [Word] {
    unimplemented!()
}
