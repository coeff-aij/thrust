use crate::thrust_models;
use std::marker::PhantomData;

use thrust_models::model::{BitVec, Seq};
use thrust_models::{exists, forall};

use crate::rustc_index::{Idx, IdxRange};
use crate::case_study::USize;

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
    // Rewrite (rewrites.md S11): the number of members, proof-only (`Ghost` has no runtime data).
    // The bodies are trusted, so the contracts of `new_empty`, `insert` and `insert_all` define it.
    card: thrust_models::Ghost<USize>,
}

#[thrust_macros::context]
impl<T: Idx> DenseBitSet<T> {
    /// `i` is a member of the set: bit `i % 64` of word `i / 64`, rustc's layout.
    #[thrust_macros::predicate]
    pub(crate) fn mem(self, i: usize) -> bool {
        (BitVec::<64, false>::from_int(self.1[i / 64]) >> BitVec::from_int(i % 64))
            & BitVec::from_int(1)
            == BitVec::from_int(1)
    }

    /// `dist` is `self` with `i` inserted: same domain, and bit `i % 64` of word `i / 64` set.
    #[thrust_macros::predicate]
    fn inserted(self, i: usize, dist: Self) -> bool {
        dist.0 == self.0
            && forall(|w: USize| {
                !(w == (BitVec::<64, false>::from_int(self.1[i / 64])
                    | (BitVec::from_int(1) << BitVec::from_int(i % 64)))
                .to_int())
                    || dist.1 == self.1.store(i / 64, w)
            })
    }

    /// `forall i: !Self::mem(self, i)` over the positions the word sequence
    /// holds. A sequence has no constant literal, so this cannot be one
    /// equality the way it was over an array: it is a guarded `forall`, which
    /// in the postcondition of a trusted function becomes a universally
    /// quantified *assumption*.
    #[thrust_macros::predicate]
    fn no_mem(self) -> bool {
        forall(|k: USize| !(0 <= k && k < self.1.len()) || self.1[k] == 0)
    }

    /// The word sequence holds `num_words(domain_size)` words, so every word `mem` and
    /// `inserted` read exists.
    #[thrust_macros::predicate]
    pub(crate) fn words_cover_domain(self) -> bool {
        self.1.len() == (self.0 + 63) / 64
    }

    #[inline]
    #[thrust_macros::ensures(result.0 == domain_size)]
    #[thrust_macros::ensures(Self::no_mem(result))]
    #[thrust_macros::ensures(Self::words_cover_domain(result))]
    #[thrust_macros::ensures(result.3 == 0)]
    pub fn new_empty(domain_size: usize) -> DenseBitSet<T> {
        let num_words = num_words(domain_size);
        DenseBitSet {
            domain_size,
            words: vec![0; num_words],
            marker: PhantomData,
            card: thrust_macros::ghost!(|| -> USize { 0 }),
        }
    }

    #[thrust_macros::requires(Self::words_cover_domain(*self))]
    fn clear_excess_bits(&mut self) {
        clear_excess_bits_in_final_word(self.domain_size, &mut self.words);
    }

    #[thrust::callable]
    pub fn count(&self) -> usize {
        count_ones(&self.words)
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(forall(|i: USize| <T as Idx>::index_is(elem, i) ==> i < (*self).0))]
    #[thrust_macros::requires(Self::words_cover_domain(*self))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && (result == true) ==> Self::mem(*self, i)))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && Self::mem(*self, i) ==> (result == true)))]
    pub fn contains(&self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let (word_index, mask) = word_index_and_mask(elem);
        (self.words[word_index] & mask) != 0
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(forall(|i: USize| <T as Idx>::index_is(elem, i) ==> i < (*self).0))]
    #[thrust_macros::ensures((!self).0 == (*self).0)]
    #[thrust_macros::ensures(Self::words_cover_domain(*self) ==> Self::words_cover_domain(!self))]
    // `Self::inserted` gives, for `i` the index of `elem`:
    //   `Self::mem(!self, i)`, and
    //   `forall j != i: Self::mem(!self, j) <==> Self::mem(*self, j)`.
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i)
        ==> Self::inserted(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && (result == true) ==> !Self::mem(*self, i)))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && Self::mem(*self, i) ==> (result == false)))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && !Self::mem(*self, i) ==> (result == true)))]
    #[thrust_macros::ensures((result == true) ==> (!self).3 == (*self).3 + 1)]
    #[thrust_macros::ensures((result == false) ==> (!self).3 == (*self).3)]
    #[thrust_macros::ensures(0 <= (!self).3 && (!self).3 <= (!self).0)]
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

    // Trusted: with `<[T]>::fill` specified, the bits below `domain_size` kept by
    // `clear_excess_bits` and `card` set by `ghost!`, the solver gives no answer at 120 s.
    #[thrust::trusted]
    #[thrust_macros::ensures((!self).0 == (*self).0)]
    #[thrust_macros::ensures(Self::words_cover_domain(*self) ==> Self::words_cover_domain(!self))]
    #[thrust_macros::ensures(forall(|i: USize| i < (*self).0 ==> Self::mem(!self, i)))]
    #[thrust_macros::ensures((!self).3 == (*self).0)]
    pub fn insert_all(&mut self) {
        self.words.fill(!0);
        self.clear_excess_bits();
    }

    // Trusted: the iterator's ghost state is the set's members, which relates the words to the
    // ghost count only through the trusted contracts above.
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::ensures(result.4 == (*self).0 && result.5 == 0)]
    #[thrust_macros::ensures(0 <= result.6 && result.6 <= (*self).0)]
    #[thrust_macros::ensures(result.6 == (*self).3)]
    #[thrust_macros::ensures(forall(|k: USize| !(result.7[k] != 0) || (0 <= k && k < (*self).0 && Self::mem(*self, k))))]
    #[thrust_macros::ensures(forall(|k: USize| !(0 <= k && k < (*self).0 && Self::mem(*self, k)) || result.7[k] != 0))]
    pub fn iter(&self) -> BitIter<'_, T> {
        BitIter::new(&self.words)
    }
}

/// Own iterator standing in for `slice::Iter<'a, Word>` (whose raw pointer
/// fields have no model in Thrust): yields `&words[0]`, ..., `&words[len - 1]`.
pub struct WordIter<'a> {
    pub(crate) words: &'a [Word],
    pub(crate) pos: usize,
}

// `WordIter`'s model is the `(words, pos)` pair: `words` is the `&[Word]`
// field's model (`&Seq<Int>`), so the predicates read `self.0` (the sequence)
// and `self.1` (the cursor) and can index by the model `Int`.
#[thrust_macros::context]
impl<'a> WordIter<'a> {
    /// `self.words.len() == n`.
    #[thrust_macros::predicate]
    fn words_len_is(self, n: USize) -> bool {
        n == self.0.len()
    }

    /// `self.words[i] == w`.
    #[thrust_macros::predicate]
    fn word_is(self, i: USize, w: USize) -> bool {
        w == self.0[i]
    }

    /// `dist.words == self.words`.
    #[thrust_macros::predicate]
    fn same_words(self, dist: Self) -> bool {
        *dist.0 == *self.0
    }

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.1 == 0)]
    #[thrust_macros::ensures(Self::words_len_is(result, (*words).len()))]
    #[thrust_macros::ensures(forall(|i: USize| Self::word_is(result, i, (*words)[i])))]
    pub(crate) fn new(words: &'a [Word]) -> WordIter<'a> {
        WordIter { words, pos: 0 }
    }
}

// The contract of `next` is an `extern_spec_fn` wrapper, as for `IdxRange::next` (idx.rs).
// `Option<&'a Word>` models as `Option<&'a Int>`, so the yielded word is named by
// `exists(|x: Int| result == Some(&x) && ..)`.
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

#[thrust_macros::context]
impl<'a> WordIter<'a> {
    #[thrust::extern_spec_fn]
    #[thrust_macros::ensures(Self::same_words(*it, !it))]
    #[thrust_macros::ensures(forall(|n: USize, p: USize|
        Self::words_len_is(*it, n) && p == (*it).1
            ==> (p < n ==> exists(|x: USize| result == Some(&x) && Self::word_is(*it, p, x))
                    && p + 1 == (!it).1)
                && (n <= p ==> result == None && (!it).1 == (*it).1)))]
    fn _extern_spec_next(it: &mut WordIter<'a>) -> Option<&'a Word> {
        <WordIter<'a> as Iterator>::next(it)
    }
}

pub struct BitIter<'a, T: Idx> {
    word: Word,

    offset: usize,

    iter: WordIter<'a>,

    marker: PhantomData<T>,

    // Rewrite (rewrites.md S11): proof-only. A bound on the elements, the number yielded so far,
    // the number still to come, and the members still to come as flags (non-zero at a member).
    // The trusted `iter` of `DenseBitSet` and of `BitMatrix`, the only callers of `new`, state
    // them; `new` leaves them empty.
    bound: thrust_models::Ghost<USize>,
    count: thrust_models::Ghost<USize>,
    left: thrust_models::Ghost<USize>,
    rest: thrust_models::Ghost<Seq<USize>>,
}

// `BitIter`'s model is the tuple of its fields' models,
// `(word, offset, (words, pos), marker, bound, count, left, rest)`, so that the case study's
// iterator trait can compare two states; the word array is `self.2.0`.
#[thrust_macros::context]
impl<'a, T: Idx> BitIter<'a, T> {
    /// `n == self.iter.words.len() * WORD_BITS`: the number of bits the
    /// underlying word array holds. Every index this iterator yields is
    /// `bit_pos + offset` for some bit of some word of that array, so this is
    /// a bound on it -- an abstraction, since `next`'s body is trusted and
    /// the wrapping `offset` arithmetic is not modelled.
    #[thrust_macros::predicate]
    fn bit_bound(self, n: usize) -> bool {
        n == 64 * self.2.0.len()
    }

    /// `dist.iter.words == self.iter.words`: `next` never replaces the word
    /// array, so the bound above survives a call.
    #[thrust_macros::predicate]
    fn same_words(self, dist: Self) -> bool {
        *dist.2.0 == *self.2.0
    }
}

// Outside the `#[thrust_macros::context]` block, so that `ghost!` adds no `Model` bound on `T`.
// Its only callers, the two trusted `iter`s, state the ghost fields.
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
            bound: thrust_macros::ghost!(|| -> USize { 0 }),
            count: thrust_macros::ghost!(|| -> USize { 0 }),
            left: thrust_macros::ghost!(|| -> USize { 0 }),
            rest: thrust_macros::ghost!(|| -> Seq<USize> { Seq::empty() }),
        }
    }
}

// `BitIter` implements the case study's iterator trait (rewrites.md R9), which `layout()`'s `Map`
// and eligibility's `enumerate` need. Every yielded element is below the bound and the word
// array's bit count, and the elements are distinct, so count + left stays at most the bound.
// `left` makes completion observable: the iterator completes with nothing left, which `Map`'s
// `reinitialize` in `layout()` needs. `rest` says which elements come: a yielded element leaves
// it, an element not yielded stays, and none joins; at completion it has no member below the
// bound. `next` builds its item with `T::new`, which panics unless `can_new` holds; the model
// does not say which bit comes next, so every index below the bound must be buildable.
#[thrust_macros::context]
impl<'a, T: Idx + thrust_models::Model> crate::case_study::iter::Iterator for BitIter<'a, T>
where
    T::Ty: PartialEq,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.next_bit()
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        0 <= self.5
            && 0 <= self.6
            && self.5 + self.6 <= self.4
            && forall(|k: USize| !(0 <= k && k < self.4) || <T as Idx>::can_new(k))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        Self::same_words(self, o)
            && forall(|n: USize, i: USize, k: USize|
                !(Self::bit_bound(self, n) && 0 <= i && i < visited.len() && <T as Idx>::index_is(visited[i], k))
                    || k < n)
            && self.4 == o.4
            && o.5 == self.5 + visited.len()
            && o.5 <= self.4
            && o.6 + visited.len() == self.6
            && 0 <= o.6
            && forall(|i: USize, k: USize|
                !(0 <= i && i < visited.len() && <T as Idx>::index_is(visited[i], k))
                    || (k < self.4 && self.7[k] != 0 && o.7[k] == 0))
            && forall(|k: USize| !(o.7[k] != 0) || self.7[k] != 0)
            && forall(|k: USize|
                !(self.7[k] != 0
                    && forall(|i: USize| !(0 <= i && i < visited.len()) || !<T as Idx>::index_is(visited[i], k)))
                    || o.7[k] != 0)
    }

    // The fields may change on the way to the end (zero words are skipped), the ghost state does
    // not.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        Self::same_words(*self, !self)
            && (*self).6 == 0
            && forall(|k: USize| !(0 <= k && k < (*self).4) || (*self).7[k] == 0)
            && (!self).4 == (*self).4
            && (!self).5 == (*self).5
            && (!self).6 == (*self).6
            && (!self).7 == (*self).7
    }
}

// The trusted body of `next`, rustc's bit arithmetic, which Thrust does not model: Thrust trusts a
// function only on its own contract, and the method of an impl of the local trait has the trait's.
#[thrust_macros::context]
impl<'a, T: Idx + thrust_models::Model> BitIter<'a, T>
where
    T::Ty: PartialEq,
{
    #[thrust::trusted]
    #[thrust_macros::requires(<Self as crate::case_study::iter::Iterator>::invariant(*self))]
    #[thrust_macros::ensures(
        <Self as crate::case_study::iter::Iterator>::invariant(!self)
            && (result == None ==> <Self as crate::case_study::iter::Iterator>::completed(self))
            && forall(|x: <T as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as crate::case_study::iter::Iterator>::produces(*self, Seq::singleton(x), !self))
    )]
    fn next_bit(&mut self) -> Option<T> {
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

// #[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
// `Clone, Eq, PartialEq` commented out: same `PhantomData` ICE as above.
#[derive(/* Clone, Eq, PartialEq, */ Hash)]
pub struct BitMatrix<R: Idx, C: Idx> {
    pub(crate) num_rows: usize,
    pub(crate) num_columns: usize,
    words: Vec<Word>,
    marker: PhantomData<(R, C)>,
    // Rewrite (rewrites.md S11): proof-only, every set bit's column is below it. rustc's `new`
    // starts it at 0 and `insert` raises it past the column it sets.
    pub(crate) col_bound: thrust_models::Ghost<USize>,
}

#[thrust_macros::context]
impl<R: Idx, C: Idx> BitMatrix<R, C> {
    /// Well-formedness: `words` holds `num_words(num_columns)` words per row
    /// (the invariant `BitMatrix::new` establishes). `num_words` is
    /// `ceil(num_columns / 64)`, spelled as the word count `rw` with
    /// `64 * rw >= num_columns` and `64 * rw < num_columns + 64`.
    #[thrust_macros::predicate]
    pub(crate) fn wf(self) -> bool {
        exists(|rw: USize| {
            self.words.len() == self.num_rows * rw
                && 64 * rw >= self.num_columns
                && 64 * rw < self.num_columns + 64
        }) && 0 <= *self.col_bound && *self.col_bound <= self.num_columns
    }

    #[thrust_macros::ensures(result.start == 0)]
    #[thrust_macros::ensures(result.end == (*self).num_rows)]
    pub fn rows(&self) -> IdxRange<R> {
        IdxRange::new(0, self.num_rows)
    }

    #[thrust::callable]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(forall(|i: USize| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    #[thrust_macros::ensures(result.0 <= result.1)]
    #[thrust_macros::ensures(result.1 <= (*self).words.len())]
    fn range(&self, row: R) -> (usize, usize) {
        let words_per_row = num_words(self.num_columns);
        let start = row.index() * words_per_row;
        (start, start + words_per_row)
    }

    // Trusted, as `DenseBitSet::iter`: the iterator's ghost state is the row's members, below the
    // ghost column bound.
    #[thrust::trusted]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(forall(|i: USize| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    #[thrust_macros::ensures(result.4 == *(*self).col_bound && result.5 == 0)]
    #[thrust_macros::ensures(0 <= result.6 && result.6 <= *(*self).col_bound)]
    pub fn iter(&self, row: R) -> BitIter<'_, C> {
        assert!(row.index() < self.num_rows);
        let (start, end) = self.range(row);
        BitIter::new(&self.words[start..end])
    }

    #[thrust::callable]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(forall(|i: USize| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    pub fn count(&self, row: R) -> usize {
        let (start, end) = self.range(row);
        count_ones(&self.words[start..end])
    }
}

#[inline]
#[thrust_macros::requires(forall(|i: USize, j: USize|
    <T as Idx>::index_is(domain_size, i) && <T as Idx>::index_is(domain_size, j) ==> i == j))]
#[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(domain_size, i)
    ==> 64 * result >= i && 64 * result < i + 64))]
fn num_words<T: Idx>(domain_size: T) -> usize {
    domain_size.index().div_ceil(WORD_BITS)
}

#[inline]
// Trusted: the body verifies against this contract only with `index_is` functional, and then
// the solver gives no answer at 120 s.
#[thrust::trusted]
#[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i)
    ==> result.0 == i / 64
        && result.1 == (BitVec::<64, false>::from_int(1) << BitVec::from_int(i % 64)).to_int()))]
fn word_index_and_mask<T: Idx>(elem: T) -> (usize, Word) {
    let elem = elem.index();
    let word_index = elem / WORD_BITS;
    let mask = 1 << (elem % WORD_BITS);
    (word_index, mask)
}

#[thrust_macros::requires((*words).len() == (domain_size + 63) / 64)]
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
