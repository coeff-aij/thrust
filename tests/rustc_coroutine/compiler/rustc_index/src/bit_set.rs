use crate::thrust_models;
use std::marker::PhantomData;

use thrust_models::model::{Array, BitVec, Int, Seq};
use thrust_models::{exists, forall, Ghost};

use crate::rustc_index::{Idx, IdxRange};
use bits::{
    bit, bit_to_come, bits_clear_of, bits_to_come_at_start, bits_to_come_clear,
    bits_to_come_exhausted, bits_to_come_next_word, excess_cleared, full_word_bits, high_mask_bits,
    low_mask_bits, masked, masked_def, masked_range, set_bit, test_bit, zero_word_bits,
};
use count::{
    ones_full, ones_le, ones_le_upto, ones_past, ones_set_bit, ones_to_come, ones_to_come_at_start,
    ones_to_come_clear, ones_to_come_exhausted, ones_to_come_le, ones_to_come_next_word,
    zero_bits_ones,
};
// `ones` for stage 7's counting lemmas in rustc_abi's layout/coroutine.rs.
pub(crate) use count::ones;
use crate::IteratorSpec;
use crate::case_study::USize;

type Word = u64;
const WORD_BYTES: usize = size_of::<Word>();
const WORD_BITS: usize = WORD_BYTES * 8;

#[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
#[derive(Eq, PartialEq, Hash)]
pub struct DenseBitSet<T> {
    domain_size: usize,
    words: Vec<Word>,
    marker: PhantomData<T>,
}

#[thrust_macros::context]
impl<T: Idx> DenseBitSet<T> {
    /// `i` is a member of the set: bit `i % 64` of word `i / 64`, rustc's layout.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn mem(self, i: usize) -> bool {
        bit(self.1, i) == 1
    }

    /// `dist` is `self` with `i` inserted: same domain, and bit `i % 64` of word `i / 64` set. The
    /// new word is named as `dist.1[i / 64]`, as `store` takes a `USize`.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    fn inserted(self, i: usize, dist: Self) -> bool {
        dist.0 == self.0
            && dist.1 == self.1.store(i / 64, dist.1[i / 64])
            && dist.1[i / 64]
                == (BitVec::<64, false>::from_int(self.1[i / 64])
                    | (BitVec::from_int(1) << BitVec::from_int(i % 64)))
                .to_int()
    }

    /// `forall i: !Self::mem(self, i)` over the positions the word sequence
    /// holds. A sequence has no constant literal, so this cannot be one
    /// equality the way it was over an array: it is a guarded `forall`, which
    /// in the postcondition of a trusted function becomes a universally
    /// quantified *assumption*.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    fn no_mem(self) -> bool {
        forall(|k: USize| !(0 <= k && k < self.1.len()) || self.1[k] == 0)
    }

    /// The word sequence holds `num_words(domain_size)` words, so every word `mem` and
    /// `inserted` read exists; each word is a 64-bit value, which the model of `u64` does not
    /// bound above by default: `insert` compares the word before and after setting a bit; and no
    /// bit at or past `domain_size` is set, as rustc's `clear_excess_bits` keeps the words, so the
    /// bits `iter` yields are the members.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn words_cover_domain(self) -> bool {
        self.1.len() == (self.0 + 63) / 64
            && forall(|k: USize| !(0 <= k && k < self.1.len()) || (0 <= self.1[k] && self.1[k] <= 18446744073709551615u64))
            && forall(|p: USize| !(self.0 <= p && p < 64 * self.1.len()) || bit(self.1, p) == 0)
    }

    /// The number of members: the set bits below `domain_size`.
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub(crate) fn card(self) -> Int {
        ones(self.1, self.0)
    }

    #[thrust::reveal]
    #[inline]
    #[thrust_macros::ensures(result.0 == domain_size)]
    #[thrust_macros::ensures(Self::no_mem(result))]
    // What `no_mem` gives of the members, for the code that does not reveal `mem`.
    #[thrust_macros::ensures(forall(|i: USize| 0 <= i && i < domain_size ==> !Self::mem(result, i)))]
    #[thrust_macros::ensures(Self::words_cover_domain(result))]
    #[thrust_macros::ensures(Self::card(result) == 0)]
    pub fn new_empty(domain_size: usize) -> DenseBitSet<T> {
        let num_words = num_words(domain_size);
        let words = vec![0; num_words];
        let s = thrust_macros::ghost!(|words: Vec<Word>| -> Seq<USize> { words });
        thrust_macros::proof!(zero_bits_ones(s, domain_size));
        thrust_macros::proof!(zero_word_bits(s));
        DenseBitSet {
            domain_size,
            words,
            marker: PhantomData,
        }
    }

    #[thrust::reveal]
    fn clear_excess_bits(&mut self) {
        let words = &self.words;
        let s = thrust_macros::ghost!(|words: &Vec<Word>| -> Seq<USize> { *words });
        thrust_macros::proof!(masked_range(s, self.domain_size));
        clear_excess_bits_in_final_word(self.domain_size, &mut self.words);
    }

    pub fn count(&self) -> usize {
        count_ones(&self.words)
    }

    #[thrust::reveal]
    #[inline]
    #[thrust_macros::requires(forall(|i: USize| <T as Idx>::index_is(elem, i) ==> i < (*self).0))]
    #[thrust_macros::requires(Self::words_cover_domain(*self))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && (result == true) ==> Self::mem(*self, i)))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && Self::mem(*self, i) ==> (result == true)))]
    pub fn contains(&self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let (word_index, mask) = word_index_and_mask(elem);
        let words = &self.words;
        let s = thrust_macros::ghost!(|words: &Vec<Word>| -> Seq<USize> { *words });
        thrust_macros::proof!(test_bit(s, elem.index()));
        (self.words[word_index] & mask) != 0
    }

    #[inline]
    // The solver proves each of these `ensures` alone but gives no answer on their conjunction:
    // the roots that check this body split goals (`THRUST_SPLIT_GOALS`), one per `ensures`.
    #[thrust::reveal]
    #[thrust_macros::requires(forall(|i: USize| <T as Idx>::index_is(elem, i) ==> i < (*self).0))]
    #[thrust_macros::requires(Self::words_cover_domain(*self))]
    #[thrust_macros::ensures((!self).0 == (*self).0)]
    #[thrust_macros::ensures(Self::words_cover_domain(!self))]
    // `Self::inserted` gives, for `i` the index of `elem`, `Self::mem(!self, i)` and
    // `forall j != i: Self::mem(!self, j) <==> Self::mem(*self, j)`, stated below for the code
    // that does not reveal `mem`.
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i)
        ==> Self::inserted(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) ==> Self::mem(!self, i)))]
    #[thrust_macros::ensures(forall(|i: USize, j: USize| <T as Idx>::index_is(elem, i) && 0 <= j && j < (*self).0 && j != i
        ==> (Self::mem(!self, j) == Self::mem(*self, j))))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && (result == true) ==> !Self::mem(*self, i)))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && Self::mem(*self, i) ==> (result == false)))]
    #[thrust_macros::ensures(forall(|i: USize| <T as Idx>::index_is(elem, i) && !Self::mem(*self, i) ==> (result == true)))]
    #[thrust_macros::ensures((result == true) ==> Self::card(!self) == Self::card(*self) + 1)]
    #[thrust_macros::ensures((result == false) ==> Self::card(!self) == Self::card(*self))]
    #[thrust_macros::ensures(Self::card(!self) <= (!self).0)]
    pub fn insert(&mut self, elem: T) -> bool {
        assert!(
            elem.index() < self.domain_size,
            "inserting element at index {} but domain size is {}",
            elem.index(),
            self.domain_size,
        );
        let (word_index, mask) = word_index_and_mask(elem);
        let words = &self.words;
        let s = thrust_macros::ghost!(|words: &Vec<Word>| -> Seq<USize> { *words });
        let word_ref = &mut self.words[word_index];
        let word = *word_ref;
        let new_word = word | mask;
        *word_ref = new_word;
        thrust_macros::proof!(set_bit(s, new_word, elem.index()));
        thrust_macros::proof!(ones_set_bit(s, new_word, elem.index(), self.domain_size));
        let words = &self.words;
        let t = thrust_macros::ghost!(|words: &Vec<Word>| -> Seq<USize> { *words });
        thrust_macros::proof!(ones_le(t, self.domain_size));
        new_word != word
    }

    #[thrust::reveal]
    #[thrust_macros::requires(Self::words_cover_domain(*self))]
    #[thrust_macros::ensures((!self).0 == (*self).0)]
    #[thrust_macros::ensures(Self::words_cover_domain(!self))]
    #[thrust_macros::ensures(forall(|i: USize| 0 <= i && i < (*self).0 ==> Self::mem(!self, i)))]
    #[thrust_macros::ensures(Self::card(!self) == (*self).0)]
    pub fn insert_all(&mut self) {
        self.words.fill(!0);
        let words = &self.words;
        let s = thrust_macros::ghost!(|words: &Vec<Word>| -> Seq<USize> { *words });
        self.clear_excess_bits();
        let words = &self.words;
        let t = thrust_macros::ghost!(|words: &Vec<Word>| -> Seq<USize> { *words });
        thrust_macros::proof!(full_word_bits(t));
        thrust_macros::proof!(low_mask_bits(t, u64::MAX, self.domain_size));
        thrust_macros::proof!(filled_bits(s, self.domain_size, t));
        thrust_macros::proof!(ones_full(t, self.domain_size));
        thrust_macros::proof!(high_mask_bits(t, u64::MAX, self.domain_size));
        thrust_macros::proof!(excess_bits_clear(s, u64::MAX, self.domain_size, t));
    }

    // The ghost state (rewrites.md S11) is the set's members: `left` their count `card`, `rest`
    // their flags. They are the set bits of the words, which `next` yields, as no bit is set at or
    // past `domain_size` (`words_cover_domain`), a `usize`.
    #[inline]
    #[thrust::reveal]
    #[thrust_macros::requires(Self::words_cover_domain(*self) && (*self).0 <= 18446744073709551615usize)]
    #[thrust_macros::ensures(BitIter::<T>::tracks_words(result))]
    #[thrust_macros::ensures(result.4 == (*self).0 && result.5 == 0)]
    #[thrust_macros::ensures(0 <= result.6 && result.6 <= (*self).0)]
    #[thrust_macros::ensures(result.6 == Self::card(*self))]
    #[thrust_macros::ensures(forall(|k: USize| result.7[k] != 0 ==> (0 <= k && k < (*self).0 && Self::mem(*self, k))))]
    #[thrust_macros::ensures(forall(|k: USize| 0 <= k && k < (*self).0 && Self::mem(*self, k) ==> result.7[k] != 0))]
    pub fn iter(&self) -> BitIter<'_, T> {
        let words = &self.words;
        let mut it = BitIter::new(words);
        let domain_size = self.domain_size;
        let s = thrust_macros::ghost!(|words: &Vec<Word>| -> Seq<USize> { *words });
        thrust_macros::proof!(ones_le(s, domain_size));
        let n = thrust_macros::ghost!(|domain_size: usize| -> USize { domain_size });
        thrust_macros::proof!(ones_past(s, n, WORD_BITS * words.len()));
        thrust_macros::proof!(ones_to_come_at_start(s, WORD_BITS * words.len()));
        thrust_macros::proof!(bits_to_come_at_start(s));
        it.bound = thrust_macros::ghost!(|domain_size: usize| -> USize { domain_size });
        it.left = thrust_macros::ghost!(|words: &Vec<Word>, domain_size: usize| -> USize { ones(*words, domain_size) });
        it.rest = thrust_macros::ghost!(|words: &Vec<Word>, domain_size: usize| -> Array<USize, Int> { member_flags(*words, domain_size) });
        it
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

    #[thrust_macros::ensures(result.1 == 0 && *result.0 == *words)]
    pub(crate) fn new(words: &'a [Word]) -> WordIter<'a> {
        WordIter { words, pos: 0 }
    }
}

// `Option<&'a Word>` models as `Option<&'a Int>`, so the yielded word is named by
// `exists(|x: Int| result == Some(&x) && ..)`.
#[thrust_macros::context]
impl<'a> Iterator for WordIter<'a> {
    type Item = &'a Word;

    #[thrust_macros::ensures(Self::same_words(*self, !self))]
    #[thrust_macros::ensures(forall(|n: USize, p: USize|
        Self::words_len_is(*self, n) && p == (*self).1
            ==> (p < n ==> exists(|x: USize| result == Some(&x) && Self::word_is(*self, p, x))
                    && p + 1 == (!self).1)
                && (n <= p ==> result == None && (!self).1 == (*self).1)))]
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

// The words from the cursor on, as std.rs's `IteratorSpec` of `slice::Iter`.
#[thrust_macros::context]
impl<'a> IteratorSpec for WordIter<'a> {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.1 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<&'a Word>, o: Self) -> bool {
        Self::same_words(self, o)
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && forall(|i: USize| !(0 <= i && i < visited.len()) || visited[i] == &self.0[self.1 + i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 >= (*self).0.len() && Self::same_words(*self, !self) && (!self).1 == (*self).1
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

pub struct BitIter<'a, T: Idx> {
    word: Word,

    offset: usize,

    iter: WordIter<'a>,

    marker: PhantomData<T>,

    // Rewrite (rewrites.md S11): proof-only. A bound on the elements, the number yielded so far,
    // the number still to come, and the members still to come as flags (non-zero at a member).
    // The `iter` of `DenseBitSet` and of `BitMatrix`, the only callers of `new`, set them to the
    // members (`member_flags`); `new` leaves them empty, and `next` takes out the member it yields.
    bound: thrust_models::Ghost<USize>,
    count: thrust_models::Ghost<USize>,
    left: thrust_models::Ghost<USize>,
    rest: thrust_models::Ghost<Array<USize, Int>>,
}

// `BitIter`'s model is the tuple of its fields' models,
// `(word, offset, (words, pos), marker, bound, count, left, rest)`, so that std.rs's
// `IteratorSpec` impl can compare two states; the word array is `self.2.0`.
#[thrust_macros::context]
impl<'a, T: Idx> BitIter<'a, T> {
    /// `n == self.iter.words.len() * WORD_BITS`: the number of bits the
    /// underlying word array holds. Every index this iterator yields is
    /// `bit_pos + offset` for some bit of some word of that array, so this is
    /// a bound on it.
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

    /// The ghost state is what the words have still to yield (`bit_to_come`): with the cursor at
    /// `pos`, `word` holds the bits of word `pos - 1` not yet yielded and `offset` is its first
    /// index, `64 * (pos - 1)` while that is below the bound (it wraps from `usize::MAX - 63` to 0
    /// at the first word); `rest` flags the bits to come below the bound, a `usize`, `left` counts
    /// them, and none lies at or past it. The words not yet read are 64-bit values.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn tracks_words(self) -> bool {
        0 <= self.2.1
            && self.2.1 <= self.2.0.len()
            && self.4 <= 64 * self.2.0.len()
            && self.4 <= 18446744073709551615usize
            && 0 <= self.0
            && self.0 <= 18446744073709551615u64
            && forall(|i: USize| !(self.2.1 <= i && i < self.2.0.len())
                || (0 <= self.2.0[i] && self.2.0[i] <= 18446744073709551615u64))
            && (!(self.2.1 == 0) || (self.0 == 0 && self.1 == 18446744073709551552usize))
            && (!(0 < self.2.1) || self.1 == 64 * (self.2.1 - 1) || self.4 <= 64 * (self.2.1 - 1))
            && self.6 == ones_to_come(*self.2.0, self.2.1, self.0, 64 * self.2.0.len())
            && forall(|k: USize| (self.7[k] != 0)
                == (0 <= k && k < self.4 && bit_to_come(*self.2.0, self.2.1, self.0, k) == 1))
            && forall(|p: USize| !(self.4 <= p && p < 64 * self.2.0.len())
                || bit_to_come(*self.2.0, self.2.1, self.0, p) == 0)
    }
}

// Outside the `#[thrust_macros::context]` block, so that `ghost!` adds no `Model` bound on `T`.
// Its only callers, the two `iter`s, set the ghost fields.
impl<'a, T: Idx> BitIter<'a, T> {
    #[inline]
    fn new(words: &'a [Word]) -> BitIter<'a, T> {
        let rest = thrust_macros::ghost!(|| -> Array<USize, Int> { no_flags() });
        BitIter {
            word: 0,
            offset: usize::MAX - (WORD_BITS - 1),
            iter: WordIter::new(words),
            marker: PhantomData,
            bound: thrust_macros::ghost!(|| -> USize { 0 }),
            count: thrust_macros::ghost!(|| -> USize { 0 }),
            left: thrust_macros::ghost!(|| -> USize { 0 }),
            rest,
        }
    }
}

// `BitIter` implements std.rs's `IteratorSpec`, which `layout()`'s `Map` and eligibility's
// `enumerate` need. Every yielded element is below the bound and the word
// array's bit count, and the elements are distinct, so count + left stays at most the bound.
// `left` makes completion observable: the iterator completes with nothing left, which `Map`'s
// `reinitialize` in `layout()` needs. `rest` says which elements come: a yielded element leaves
// it, an element not yielded stays, and none joins; at completion it has no member below the
// bound. `next` builds its item with `T::new`, which panics unless `can_new` holds; the model
// does not say which bit comes next, so every index below the bound must be buildable.
#[thrust_macros::context]
impl<'a, T: Idx + thrust_models::Model> Iterator for BitIter<'a, T>
{
    type Item = T;

    #[thrust::reveal]
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*self))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!self)
            && (result == None ==> <Self as IteratorSpec>::completed(self))
            && forall(|x: <T as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as IteratorSpec>::produces(*self, Seq::singleton(x), !self))
    )]
    fn next(&mut self) -> Option<T> {
        // Rewrite (rewrites.md S11): `self` is named `this`, which the loop invariant reads, and
        // the ghost state drops the member yielded.
        let this = self;
        loop {
            thrust_macros::invariant!(
                |this: &mut BitIter<'a, T>, self: thrust_models::FnParam<&mut BitIter<'a, T>>|
                    !this == !self.at_entry()
                        && <BitIter<'a, T> as IteratorSpec>::inv(*this)
                        && *(*this).2.0 == *(*self.at_entry()).2.0
                        && (*this).4 == (*self.at_entry()).4
                        && (*this).5 == (*self.at_entry()).5
                        && (*this).6 == (*self.at_entry()).6
                        && (*this).7 == (*self.at_entry()).7
            );
            let s = thrust_macros::ghost!(|this: &mut BitIter<'a, T>| -> Seq<USize> { *(*this).2.0 });
            if this.word != 0 {
                let bit_pos = this.word.trailing_zeros() as usize;
                let word = thrust_macros::ghost!(|this: &mut BitIter<'a, T>| -> USize { (*this).0 });
                this.word ^= 1 << bit_pos;
                thrust_macros::proof!(bits_to_come_clear(s, this.iter.pos, word, bit_pos, this.word));
                thrust_macros::proof!(ones_to_come_clear(s, this.iter.pos, word, bit_pos, this.word, WORD_BITS * this.iter.words.len()));
                thrust_macros::proof!(ones_to_come_le(s, this.iter.pos, this.word, WORD_BITS * this.iter.words.len()));
                this.count = thrust_macros::ghost!(|this: &mut BitIter<'a, T>| -> USize { (*this).5 + 1 });
                this.left = thrust_macros::ghost!(|this: &mut BitIter<'a, T>| -> USize { (*this).6 - 1 });
                this.rest = thrust_macros::ghost!(|this: &mut BitIter<'a, T>, bit_pos: usize| -> Array<USize, Int> {
                    without_flag((*this).7, bit_pos + (*this).1)
                });
                return Some(T::new(bit_pos + this.offset));
            }

            thrust_macros::proof!(bits_to_come_exhausted(s, this.iter.pos));
            thrust_macros::proof!(ones_to_come_exhausted(s, this.iter.pos, WORD_BITS * this.iter.words.len()));
            this.word = *this.iter.next()?;
            this.offset = this.offset.wrapping_add(WORD_BITS);
            thrust_macros::proof!(bits_to_come_next_word(s, this.iter.pos));
            thrust_macros::proof!(ones_to_come_next_word(s, this.iter.pos, WORD_BITS * this.iter.words.len()));
        }
    }
}

#[thrust_macros::context]
impl<'a, T: Idx + thrust_models::Model> IteratorSpec for BitIter<'a, T>
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.5
            && 0 <= self.6
            && self.5 + self.6 <= self.4
            && forall(|k: USize| !(0 <= k && k < self.4) || <T as Idx>::can_new(k))
            && Self::tracks_words(self)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool {
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

#[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
// `Clone, Eq, PartialEq` commented out: the ghost field `col_bound` (rewrites.md S11) has no
// executable `clone` or `eq`.
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
    /// `64 * rw >= num_columns` and `64 * rw < num_columns + 64`; the column count is a `usize`
    /// and each word a 64-bit value, which the model of `u64` does not bound above by default.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn wf(self) -> bool {
        exists(|rw: USize| {
            self.words.len() == self.num_rows * rw
                && 64 * rw >= self.num_columns
                && 64 * rw < self.num_columns + 64
        }) && 0 <= *self.col_bound && *self.col_bound <= self.num_columns
            && self.num_columns <= 18446744073709551615usize
            && forall(|k: usize| !(0 <= k && k < self.words.len())
                || (0 <= self.words[k] && self.words[k] <= 18446744073709551615u64))
    }

    /// Every set bit is at a column below `b`: the fact the ghost `col_bound` stands for
    /// (rewrites.md S11). rustc's matrices have it at `b = num_columns`: `insert` asserts
    /// `column < num_columns` and `insert_all_into_row` clears the bits past it. A row holds
    /// `num_words(num_columns)` words (`wf`).
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn cols_below(self, b: usize) -> bool {
        forall(|r: usize, c: usize|
            !(0 <= r && r < self.num_rows && b <= c && c < 64 * ((self.num_columns + 63) / 64))
                || (BitVec::<64, false>::from_int(self.words[r * ((self.num_columns + 63) / 64) + c / 64])
                    >> BitVec::from_int(c % 64))
                    & BitVec::from_int(1)
                    == BitVec::from_int(0))
    }

    pub fn rows(&self) -> IdxRange<R> {
        IdxRange::new(0, self.num_rows)
    }

    #[thrust::reveal]
    #[thrust::callable]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(forall(|i: USize| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    #[thrust_macros::ensures(result.0 <= result.1)]
    #[thrust_macros::ensures(result.1 <= (*self).words.len())]
    #[thrust_macros::ensures(result.1 == result.0 + ((*self).num_columns + 63) / 64)]
    #[thrust_macros::ensures(forall(|i: USize| <R as Idx>::index_is(row, i)
        ==> result.0 == i * (((*self).num_columns + 63) / 64)))]
    fn range(&self, row: R) -> (usize, usize) {
        let words_per_row = num_words(self.num_columns);
        let start = row.index() * words_per_row;
        (start, start + words_per_row)
    }

    // The ghost state is the row's members, below the ghost column bound, which `cols_below`
    // ties to the bits.
    #[thrust::reveal]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(Self::cols_below(*self, *(*self).col_bound))]
    #[thrust_macros::requires(forall(|i: USize| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    #[thrust_macros::ensures(BitIter::<C>::tracks_words(result))]
    #[thrust_macros::ensures(result.4 == *(*self).col_bound && result.5 == 0)]
    #[thrust_macros::ensures(0 <= result.6 && result.6 <= *(*self).col_bound)]
    pub fn iter(&self, row: R) -> BitIter<'_, C> {
        assert!(row.index() < self.num_rows);
        let (start, end) = self.range(row);
        let words = &self.words[start..end];
        let mut it = BitIter::new(words);
        // The ghost column bound is at most `num_columns` (`wf`).
        let s = thrust_macros::ghost!(|words: &[Word]| -> Seq<USize> { *words });
        thrust_macros::proof!(ones_le_upto(s, self.num_columns));
        let col_bound = &self.col_bound;
        let n = thrust_macros::ghost!(|col_bound: &Ghost<USize>| -> USize { *col_bound });
        let all_words = &self.words;
        let all = thrust_macros::ghost!(|all_words: &Vec<Word>| -> Seq<USize> { *all_words });
        thrust_macros::proof!(row_cols_below(self, all, n, row.index(), start, end - start));
        thrust_macros::proof!(row_words(all, s, start, end - start));
        thrust_macros::proof!(row_bits_clear(all, s, start, end - start, n));
        thrust_macros::proof!(ones_past(s, n, WORD_BITS * words.len()));
        thrust_macros::proof!(ones_to_come_at_start(s, WORD_BITS * words.len()));
        thrust_macros::proof!(bits_to_come_at_start(s));
        it.bound = thrust_macros::ghost!(|col_bound: &Ghost<USize>| -> USize { *col_bound });
        it.left = thrust_macros::ghost!(|words: &[Word], col_bound: &Ghost<USize>| -> USize { ones(*words, *col_bound) });
        it.rest = thrust_macros::ghost!(|words: &[Word], col_bound: &Ghost<USize>| -> Array<USize, Int> { member_flags(*words, *col_bound) });
        it
    }

    #[thrust::reveal]
    #[thrust::callable]
    #[thrust_macros::requires(Self::wf(*self))]
    #[thrust_macros::requires(forall(|i: USize| <R as Idx>::index_is(row, i) ==> i < (*self).num_rows))]
    pub fn count(&self, row: R) -> usize {
        let (start, end) = self.range(row);
        count_ones(&self.words[start..end])
    }
}

/// `cols_below` at row `i` of a matrix whose words are `all`: the row's `r` words start at `a`,
/// and their bits at and past column `b` are clear. The words are 64-bit values (`wf`).
#[thrust::reveal]
#[thrust_macros::lemma]
#[thrust_macros::requires(BitMatrix::<R, C>::wf(*m) && BitMatrix::<R, C>::cols_below(*m, b))]
#[thrust_macros::requires(0 <= i && i < (*m).num_rows && all == (*m).words)]
#[thrust_macros::requires(r == (((*m).num_columns + 63) / 64) && a == i * r)]
#[thrust_macros::ensures(forall(|c: USize| !(b <= c && c < 64 * r)
    || (BitVec::<64, false>::from_int(all[a + c / 64]) >> BitVec::from_int(c % 64)) & BitVec::from_int(1)
        == BitVec::from_int(0)))]
#[thrust_macros::ensures(forall(|k: USize| !(0 <= k && k < all.len()) || (0 <= all[k] && all[k] <= 18446744073709551615u64)))]
fn row_cols_below<R: Idx, C: Idx>(
    m: &BitMatrix<R, C>,
    all: Ghost<Seq<USize>>,
    b: Ghost<USize>,
    i: usize,
    a: usize,
    r: usize,
) {}

/// The `r` words of `all` from `a`, `s`, are those words, 64-bit values when `all`'s are.
#[thrust_macros::lemma]
#[thrust_macros::requires(0 <= a && 0 <= r && a + r <= all.len() && s == all.subsequence(a, a + r))]
#[thrust_macros::requires(forall(|k: USize| !(0 <= k && k < all.len()) || (0 <= all[k] && all[k] <= 18446744073709551615u64)))]
#[thrust_macros::ensures(s.len() == r)]
#[thrust_macros::ensures(forall(|k: USize| !(0 <= k && k < r) || s[k] == all[a + k]))]
#[thrust_macros::ensures(forall(|k: USize| !(0 <= k && k < s.len()) || (0 <= s[k] && s[k] <= 18446744073709551615u64)))]
fn row_words(all: Ghost<Seq<USize>>, s: Ghost<Seq<USize>>, a: usize, r: usize) {}

/// The `r` words `s` of `all` from `a` have no bit set at or past `b` when `all`'s bits there
/// are clear.
#[thrust_macros::lemma]
#[thrust_macros::requires(0 <= a && 0 <= r && s.len() == r)]
#[thrust_macros::requires(forall(|k: USize| !(0 <= k && k < r) || s[k] == all[a + k]))]
#[thrust_macros::requires(forall(|c: USize| !(b <= c && c < 64 * r)
    || (BitVec::<64, false>::from_int(all[a + c / 64]) >> BitVec::from_int(c % 64)) & BitVec::from_int(1)
        == BitVec::from_int(0)))]
#[thrust_macros::ensures(forall(|p: USize| !(b <= p && p < 64 * s.len()) || bit(s, p) == 0))]
fn row_bits_clear(all: Ghost<Seq<USize>>, s: Ghost<Seq<USize>>, a: usize, r: usize, b: Ghost<USize>) {
    bits_clear_of(s);
}

/// The flags of an iterator with no member to come.
#[thrust_macros::logic]
fn no_flags() -> Array<USize, Int> {
    Array::<USize, Int>::from_fn(|k: USize| no_flag(k))
}

#[thrust_macros::logic]
fn no_flag(_k: USize) -> Int {
    0
}

/// `flags` with the member `k` taken out: the ghost `rest` after `next` yields `k`.
#[thrust_macros::logic]
fn without_flag(flags: Array<USize, Int>, k: USize) -> Array<USize, Int> {
    flags.store(k, no_flag(k))
}

/// The members among the first `n` bits of `words` as flags, 1 at a member and 0 elsewhere: the
/// ghost `rest` of a `BitIter` over `words` that yields the bits below `n`.
#[thrust_macros::logic]
fn member_flags(words: Seq<USize>, n: USize) -> Array<USize, Int> {
    Array::<USize, Int>::from_fn(|k: USize| member_flag(words, n, k))
}

#[thrust_macros::logic]
fn member_flag(words: Seq<USize>, n: USize, k: USize) -> Int {
    if 0 <= k && k < n && bit(words, k) == 1 { 1 } else { 0 }
}

#[inline]
fn num_words<T: Idx>(domain_size: T) -> usize {
    domain_size.index().div_ceil(WORD_BITS)
}

#[inline]
fn word_index_and_mask<T: Idx>(elem: T) -> (usize, Word) {
    let elem = elem.index();
    let word_index = elem / WORD_BITS;
    let mask = 1 << (elem % WORD_BITS);
    (word_index, mask)
}

#[thrust_macros::requires((*words).len() == (domain_size + 63) / 64)]
#[thrust_macros::ensures(excess_cleared(*words, domain_size, !words))]
fn clear_excess_bits_in_final_word(domain_size: usize, words: &mut [Word]) {
    let num_bits_in_final_word = domain_size % WORD_BITS;
    if num_bits_in_final_word > 0 {
        thrust_macros::proof!(masked_def(words[words.len() - 1], domain_size));
        let mask = (1 << num_bits_in_final_word) - 1;
        words[words.len() - 1] &= mask;
    }
}

/// The bit-level facts the bit sets rest on. `bit` is opaque outside this module, so the
/// counting lemmas in `count` and the bit sets' contracts read it as a predicate symbol and the
/// bit-vector arithmetic stays in the lemmas below, as Verus keeps `bit_vector` proofs apart.
mod bits {
    use crate::thrust_models;
    use thrust_models::model::{int_lit, BitVec, Int, Seq};
    use thrust_models::{forall, Ghost};

    use crate::case_study::USize;

    /// Bit `i % 64` of word `i / 64`, rustc's layout, as 1 or 0.
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub(crate) fn bit(words: Seq<USize>, i: USize) -> Int {
        if (BitVec::<64, false>::from_int(words[i / 64]) >> BitVec::from_int(i % 64))
            & BitVec::from_int(1)
            == BitVec::from_int(1)
        {
            1
        } else {
            0
        }
    }

    /// A bit is 1 or 0.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(bit(s, p) == 0 || bit(s, p) == 1)]
    pub(crate) fn bit_range(s: Ghost<Seq<USize>>, p: usize) {}

    /// The word `x` with its bits at and past `n % 64` cleared, as rustc's
    /// `clear_excess_bits_in_final_word` masks the last word of a domain of `n` bits. Opaque, so
    /// that a query that only carries the word along has no bit-vector term in it.
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub(crate) fn masked(x: USize, n: USize) -> Int {
        (BitVec::<64, false>::from_int(x)
            & BitVec::from_int(
                (BitVec::<64, false>::from_int(1) << (BitVec::from_int(n % 64) & BitVec::from_int(63)))
                    .to_int()
                    - 1,
            ))
        .to_int()
    }

    /// The masked last word of `s` is a 64-bit value.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(0 <= masked(s[s.len() - 1], n) && masked(s[s.len() - 1], n) <= 18446744073709551615u64)]
    pub(crate) fn masked_range(s: Ghost<Seq<USize>>, n: usize) {}

    /// `masked`'s definition, for `clear_excess_bits_in_final_word`.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(masked(x, n)
        == (BitVec::<64, false>::from_int(x)
            & BitVec::from_int(
                (BitVec::<64, false>::from_int(1) << (BitVec::from_int(n % 64) & BitVec::from_int(63)))
                    .to_int()
                    - 1,
            ))
        .to_int())]
    pub(crate) fn masked_def(x: u64, n: usize) {}

    /// `t` is `s` with the bits at and past `n` of its last word cleared, as rustc's
    /// `clear_excess_bits_in_final_word` leaves the words of a domain of `n` bits.
    #[thrust_macros::predicate]
    pub(crate) fn excess_cleared(s: Seq<USize>, n: USize, t: Seq<USize>) -> bool {
        (n % 64 == 0 && t == s)
            || (n % 64 > 0
                && t == s.store(s.len() - 1, t[s.len() - 1])
                && t[s.len() - 1] == masked(s[s.len() - 1], n))
    }

    /// Setting bit `i` in word `i / 64` to get `w`: bit `p` of the words, `p` in them, is as it was
    /// unless it is `i`, which is set.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= i && i / 64 < s.len() && 0 <= p && p / 64 < s.len())]
    #[thrust_macros::requires(w == (BitVec::<64, false>::from_int(s[i / 64])
        | (BitVec::from_int(1) << BitVec::from_int(i % 64))).to_int())]
    #[thrust_macros::ensures(bit(s.store(i / 64, w), i) == 1)]
    #[thrust_macros::ensures(bit(s, i) == 0 || bit(s, i) == 1)]
    #[thrust_macros::ensures(p == i || bit(s.store(i / 64, w), p) == bit(s, p))]
    pub(crate) fn set_bit_at(s: Ghost<Seq<USize>>, w: u64, i: usize, p: usize) {}

    /// `set_bit_at` for every `p` at once, as `DenseBitSet::insert` states its members, and the
    /// word, a 64-bit value, is unchanged exactly when bit `i` was set.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= i && i / 64 < s.len() && 0 <= s[i / 64] && s[i / 64] <= 18446744073709551615u64)]
    #[thrust_macros::requires(w == (BitVec::<64, false>::from_int(s[i / 64])
        | (BitVec::from_int(1) << BitVec::from_int(i % 64))).to_int())]
    // The word, restated so that the caller's `DenseBitSet::inserted` reads it after the call.
    #[thrust_macros::ensures(w == (BitVec::<64, false>::from_int(s[i / 64])
        | (BitVec::from_int(1) << BitVec::from_int(i % 64))).to_int())]
    #[thrust_macros::ensures(bit(s.store(i / 64, w), i) == 1)]
    #[thrust_macros::ensures(bit(s, i) == 0 || bit(s, i) == 1)]
    #[thrust_macros::ensures(forall(|p: USize| 0 <= p && p / 64 < s.len() && p != i
        ==> bit(s.store(i / 64, w), p) == bit(s, p)))]
    #[thrust_macros::ensures((w == s[i / 64]) == (bit(s, i) == 1))]
    pub(crate) fn set_bit(s: Ghost<Seq<USize>>, w: u64, i: usize) {}

    /// A zero word has no bit set.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= p)]
    #[thrust_macros::ensures(s[p / 64] == 0 ==> bit(s, p) == 0)]
    pub(crate) fn zero_word_bit(s: Ghost<Seq<USize>>, p: usize) {}

    /// The bits of a word of all ones are set.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(forall(|p: USize| 0 <= p && s[p / 64] == 18446744073709551615u64 ==> bit(s, p) == 1))]
    pub(crate) fn full_word_bits(s: Ghost<Seq<USize>>) {}

    /// The bits of a zero word are clear.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(forall(|p: USize| 0 <= p && s[p / 64] == 0 ==> bit(s, p) == 0))]
    pub(crate) fn zero_word_bits(s: Ghost<Seq<USize>>) {}

    /// The word of all ones masked as `clear_excess_bits_in_final_word` masks the last word of a
    /// domain of `n` bits keeps the bits below `n % 64`.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(x == 18446744073709551615u64)]
    #[thrust_macros::ensures(forall(|p: USize| 0 <= p && p % 64 < n % 64 && s[p / 64] == masked(x, n)
        ==> bit(s, p) == 1))]
    pub(crate) fn low_mask_bits(s: Ghost<Seq<USize>>, x: u64, n: usize) {}

    /// `contains`'s test of bit `i`: the word masked by `word_index_and_mask`'s mask is not zero.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= i)]
    #[thrust_macros::ensures((bit(s, i) == 1)
        == ((BitVec::<64, false>::from_int(s[i / 64])
            & BitVec::from_int((BitVec::<64, false>::from_int(1) << BitVec::from_int(i % 64)).to_int()))
            .to_int()
            != 0))]
    pub(crate) fn test_bit(s: Ghost<Seq<USize>>, i: usize) {}

    /// Bit `k` of what a `BitIter` over `words` has still to yield, its cursor at word `pos` and
    /// `word` the bits of word `pos - 1` it has not yielded: none in the words before word
    /// `pos - 1`, `word`'s in it, and the words' after it.
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub(crate) fn bit_to_come(words: Seq<USize>, pos: USize, word: USize, k: USize) -> Int {
        if pos <= 0 {
            bit(words, k)
        } else if k / 64 < pos - 1 {
            0
        } else {
            bit(words.store(pos - 1, word), k)
        }
    }

    /// A bit to come is 1 or 0.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(bit_to_come(s, pos, w, p) == 0 || bit_to_come(s, pos, w, p) == 1)]
    pub(crate) fn bit_to_come_range(s: Ghost<Seq<USize>>, pos: usize, w: u64, p: usize) {}

    /// Before the first word is read, the bits to come are the words' bits.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(bit_to_come(s, int_lit(0), int_lit(0), p) == bit(s, p))]
    pub(crate) fn bit_to_come_at_start(s: Ghost<Seq<USize>>, p: usize) {}

    /// `bit_to_come_at_start` at every bit.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(forall(|p: USize| bit_to_come(s, int_lit(0), int_lit(0), p) == bit(s, p)))]
    pub(crate) fn bits_to_come_at_start(s: Ghost<Seq<USize>>) {}

    /// Reading word `pos - 1` into the emptied word leaves the bits to come as they were.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 < pos && pos <= s.len() && 0 <= p && p < 64 * s.len())]
    #[thrust_macros::ensures(bit_to_come(s, pos, s[pos - 1], p) == bit_to_come(s, pos - 1, int_lit(0), p))]
    pub(crate) fn bit_to_come_next_word(s: Ghost<Seq<USize>>, pos: usize, p: usize) {}

    /// `bit_to_come_next_word` at every bit of the words.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 < pos && pos <= s.len())]
    #[thrust_macros::ensures(forall(|p: USize| !(0 <= p && p < 64 * s.len())
        || bit_to_come(s, pos, s[pos - 1], p) == bit_to_come(s, pos - 1, int_lit(0), p)))]
    pub(crate) fn bits_to_come_next_word(s: Ghost<Seq<USize>>, pos: usize) {}

    /// The bit `b` that `u64::trailing_zeros` names in a nonzero 64-bit word `w` is set.
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= w && w <= 18446744073709551615u64 && w != 0 && 0 <= b && b <= 64)]
    #[thrust_macros::requires((b == 64) == (BitVec::<64, false>::from_int(w) == BitVec::from_int(0)))]
    #[thrust_macros::requires((b != 64)
        == ((BitVec::<64, false>::from_int(w) << BitVec::from_int(63 - b))
            == (BitVec::<64, false>::from_int(1) << BitVec::from_int(63))))]
    #[thrust_macros::ensures(b < 64)]
    #[thrust_macros::ensures((BitVec::<64, false>::from_int(w) >> BitVec::from_int(b)) & BitVec::from_int(1) == BitVec::from_int(1))]
    pub(crate) fn lowest_bit_set(w: Ghost<USize>, b: usize) {}

    /// `1 << b`, computed on a `u64`, as a bit-vector.
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= b && b < 64)]
    #[thrust_macros::requires(u == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(b) & BitVec::from_int(63))).to_int())]
    #[thrust_macros::ensures(BitVec::<64, false>::from_int(u) == (BitVec::<64, false>::from_int(1) << BitVec::from_int(b)))]
    fn shifted_one(b: usize, u: u64) {}

    /// `w ^ u`, computed on a `u64`, as a bit-vector.
    #[thrust_macros::lemma]
    #[thrust_macros::requires(v == (BitVec::<64, false>::from_int(w) ^ BitVec::from_int(u)).to_int())]
    #[thrust_macros::ensures(BitVec::<64, false>::from_int(v) == (BitVec::<64, false>::from_int(w) ^ BitVec::from_int(u)))]
    #[thrust_macros::ensures(0 <= v && v <= 18446744073709551615u64)]
    fn xored(w: Ghost<USize>, u: u64, v: u64) {}

    /// `v`, computed as `w ^ (1 << b)` on a `u64`, is `w` with bit `b` flipped.
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= b && b < 64)]
    #[thrust_macros::requires(v == (BitVec::<64, false>::from_int(w)
        ^ BitVec::from_int((BitVec::<64, false>::from_int(1) << (BitVec::from_int(b) & BitVec::from_int(63))).to_int()))
        .to_int())]
    #[thrust_macros::ensures(BitVec::<64, false>::from_int(v) == (BitVec::<64, false>::from_int(w) ^ (BitVec::<64, false>::from_int(1) << BitVec::from_int(b))))]
    #[thrust_macros::ensures(0 <= v && v <= 18446744073709551615u64)]
    pub(crate) fn flipped_word(w: Ghost<USize>, b: usize, v: u64) {
        shifted_one(b, 1 << b);
        xored(w, 1 << b, v);
    }

    /// Flipping the set bit `b` of `w` clears it and keeps the others: bit `j` of the result.
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= b && b < 64 && 0 <= j && j < 64)]
    #[thrust_macros::requires((BitVec::<64, false>::from_int(w) >> BitVec::from_int(b)) & BitVec::from_int(1) == BitVec::from_int(1))]
    #[thrust_macros::requires(BitVec::<64, false>::from_int(v) == (BitVec::<64, false>::from_int(w) ^ (BitVec::<64, false>::from_int(1) << BitVec::from_int(b))))]
    #[thrust_macros::ensures(((BitVec::<64, false>::from_int(v) >> BitVec::from_int(j)) & BitVec::from_int(1) == BitVec::from_int(1))
        == (j != b && (BitVec::<64, false>::from_int(w) >> BitVec::from_int(j)) & BitVec::from_int(1) == BitVec::from_int(1)))]
    pub(crate) fn flipped_bit(w: Ghost<USize>, b: usize, v: u64, j: usize) {}

    /// `flipped_bit` at every bit.
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= b && b < 64)]
    #[thrust_macros::requires((BitVec::<64, false>::from_int(w) >> BitVec::from_int(b)) & BitVec::from_int(1) == BitVec::from_int(1))]
    #[thrust_macros::requires(BitVec::<64, false>::from_int(v) == (BitVec::<64, false>::from_int(w) ^ (BitVec::<64, false>::from_int(1) << BitVec::from_int(b))))]
    #[thrust_macros::ensures(forall(|j: USize| !(0 <= j && j < 64)
        || ((BitVec::<64, false>::from_int(v) >> BitVec::from_int(j)) & BitVec::from_int(1) == BitVec::from_int(1))
            == (j != b && (BitVec::<64, false>::from_int(w) >> BitVec::from_int(j)) & BitVec::from_int(1) == BitVec::from_int(1))))]
    pub(crate) fn flipped_bits(w: Ghost<USize>, b: usize, v: u64) {}

    /// Clearing in `w` the bit `b` that `u64::trailing_zeros` names, to get `v`, takes bit
    /// `64 * (pos - 1) + b` out of the bits to come and leaves the others.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 < pos && pos <= s.len() && 0 <= p && p < 64 * s.len())]
    #[thrust_macros::requires(0 <= w && w <= 18446744073709551615u64 && w != 0 && 0 <= b && b <= 64)]
    #[thrust_macros::requires((b == 64) == (BitVec::<64, false>::from_int(w) == BitVec::from_int(0)))]
    #[thrust_macros::requires((b != 64)
        == ((BitVec::<64, false>::from_int(w) << BitVec::from_int(63 - b))
            == (BitVec::<64, false>::from_int(1) << BitVec::from_int(63))))]
    #[thrust_macros::requires(v == (BitVec::<64, false>::from_int(w)
        ^ BitVec::from_int((BitVec::<64, false>::from_int(1) << (BitVec::from_int(b) & BitVec::from_int(63))).to_int()))
        .to_int())]
    #[thrust_macros::ensures(b < 64 && 0 <= v && v <= 18446744073709551615u64)]
    #[thrust_macros::ensures(p == 64 * (pos - 1) + b
        ==> (bit_to_come(s, pos, w, p) == 1 && bit_to_come(s, pos, v, p) == 0))]
    #[thrust_macros::ensures(p != 64 * (pos - 1) + b ==> bit_to_come(s, pos, v, p) == bit_to_come(s, pos, w, p))]
    pub(crate) fn bit_to_come_clear(s: Ghost<Seq<USize>>, pos: usize, w: Ghost<USize>, b: usize, v: u64, p: usize) {
        lowest_bit_set(w, b);
        flipped_word(w, b, v);
        flipped_bit(w, b, v, p % 64);
    }

    /// `bit_to_come_clear` at every bit of the words.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 < pos && pos <= s.len())]
    #[thrust_macros::requires(0 <= w && w <= 18446744073709551615u64 && w != 0 && 0 <= b && b <= 64)]
    #[thrust_macros::requires((b == 64) == (BitVec::<64, false>::from_int(w) == BitVec::from_int(0)))]
    #[thrust_macros::requires((b != 64)
        == ((BitVec::<64, false>::from_int(w) << BitVec::from_int(63 - b))
            == (BitVec::<64, false>::from_int(1) << BitVec::from_int(63))))]
    #[thrust_macros::requires(v == (BitVec::<64, false>::from_int(w)
        ^ BitVec::from_int((BitVec::<64, false>::from_int(1) << (BitVec::from_int(b) & BitVec::from_int(63))).to_int()))
        .to_int())]
    #[thrust_macros::ensures(b < 64 && 0 <= v && v <= 18446744073709551615u64)]
    #[thrust_macros::ensures(bit_to_come(s, pos, w, 64 * (pos - 1) + b) == 1
        && bit_to_come(s, pos, v, 64 * (pos - 1) + b) == 0)]
    #[thrust_macros::ensures(forall(|p: USize| !(0 <= p && p < 64 * s.len() && p != 64 * (pos - 1) + b)
        || bit_to_come(s, pos, v, p) == bit_to_come(s, pos, w, p)))]
    pub(crate) fn bits_to_come_clear(s: Ghost<Seq<USize>>, pos: usize, w: Ghost<USize>, b: usize, v: u64) {
        lowest_bit_set(w, b);
        flipped_word(w, b, v);
        flipped_bits(w, b, v);
    }

    /// Past the last word, with the word emptied, no bit is to come.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::requires(0 <= p && p < 64 * s.len())]
    #[thrust_macros::ensures(s.len() <= pos ==> bit_to_come(s, pos, int_lit(0), p) == 0)]
    pub(crate) fn bit_to_come_exhausted(s: Ghost<Seq<USize>>, pos: usize, p: usize) {}

    /// `bit_to_come_exhausted` at every bit of the words.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(forall(|p: USize| !(0 <= p && p < 64 * s.len() && s.len() <= pos)
        || bit_to_come(s, pos, int_lit(0), p) == 0))]
    pub(crate) fn bits_to_come_exhausted(s: Ghost<Seq<USize>>, pos: usize) {}

    /// A word masked as `clear_excess_bits_in_final_word` masks the last word of a domain of `n`
    /// bits has no bit set at or past `n % 64`.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(forall(|p: USize| 0 <= p && n % 64 <= p % 64 && s[p / 64] == masked(x, n)
        ==> bit(s, p) == 0))]
    pub(crate) fn high_mask_bits(s: Ghost<Seq<USize>>, x: u64, n: usize) {}

    /// A bit whose test in the words is 0, the form `BitMatrix::cols_below` states, is clear.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::ensures(forall(|p: USize| 0 <= p
        && (BitVec::<64, false>::from_int(s[p / 64]) >> BitVec::from_int(p % 64)) & BitVec::from_int(1)
            == BitVec::from_int(0)
        ==> bit(s, p) == 0))]
    pub(crate) fn bits_clear_of(s: Ghost<Seq<USize>>) {}
}

/// The count of set bits, `ones`, and its lemmas, by induction over the bits counted. `ones` is
/// opaque outside this module; the inductions read `bit` only through the lemmas of `bits`,
/// so each step is linear arithmetic over the function symbol `bit`.
mod count {
    use crate::thrust_models;
    use thrust_models::model::{int_lit, BitVec, Int, Seq};
    use thrust_models::{forall, Ghost};

    use super::bits::{
        bit, bit_range, bit_to_come, bit_to_come_at_start, bit_to_come_clear, bit_to_come_exhausted,
        bit_to_come_next_word, bit_to_come_range, set_bit_at, zero_word_bit,
    };
    use crate::case_study::USize;

    /// The set bits among the first `m` bits of `words`, bit `i` being bit `i % 64` of word
    /// `i / 64` as in `DenseBitSet::mem`. A count, it returns `Int`, as `card` does: at `USize`,
    /// its definition would have to show it below `2^64` under `THRUST_INT_RANGE`.
    #[thrust_macros::logic]
    #[thrust::opaque]
    #[thrust_macros::variant(m)]
    pub(crate) fn ones(words: Seq<USize>, m: USize) -> Int {
        if m <= 0 {
            0
        } else {
            ones(words, m - 1) + bit(words, m - 1)
        }
    }

    /// The first `m` bits of `s` are clear when the words they lie in are zero. `s` is a
    /// parameter, so a call states the fact at its words, not for every sequence.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::ensures(forall(|k: USize| 0 <= k && k * 64 < m ==> s[k] == 0) ==> ones(s, m) == 0)]
    pub(crate) fn zero_bits_ones(s: Ghost<Seq<USize>>, m: usize) {
        if m > 0 {
            zero_bits_ones(s, m - 1);
            zero_word_bit(s, m - 1);
        }
    }

    /// `ones` counts at most the bits it reads.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::ensures(0 <= ones(s, m) && ones(s, m) <= m)]
    pub(crate) fn ones_le(s: Ghost<Seq<USize>>, m: usize) {
        if m > 0 {
            ones_le(s, m - 1);
            bit_range(s, m - 1);
        }
    }

    /// `ones_le` at every bound up to `m`.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::ensures(forall(|j: USize| 0 <= j && j <= m ==> 0 <= ones(s, j) && ones(s, j) <= j))]
    pub(crate) fn ones_le_upto(s: Ghost<Seq<USize>>, m: usize) {
        if m > 0 {
            ones_le_upto(s, m - 1);
            ones_le(s, m);
        }
    }

    /// When the first `m` bits of `s` are set, `ones` counts each of them.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::requires(forall(|p: USize| 0 <= p && p < m ==> bit(s, p) == 1))]
    #[thrust_macros::ensures(ones(s, m) == m)]
    pub(crate) fn ones_full(s: Ghost<Seq<USize>>, m: usize) {
        if m > 0 {
            ones_full(s, m - 1);
        }
    }

    /// Setting bit `i` in word `i / 64` to get `w` adds one to the count of the first `m` bits
    /// when `i` is among them and was clear, and nothing otherwise.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::requires(0 <= i && i / 64 < s.len() && m <= 64 * s.len())]
    #[thrust_macros::requires(w == (BitVec::<64, false>::from_int(s[i / 64])
        | (BitVec::from_int(1) << BitVec::from_int(i % 64))).to_int())]
    #[thrust_macros::ensures(i < m && bit(s, i) == 0 ==> ones(s.store(i / 64, w), m) == ones(s, m) + 1)]
    #[thrust_macros::ensures(!(i < m && bit(s, i) == 0) ==> ones(s.store(i / 64, w), m) == ones(s, m))]
    pub(crate) fn ones_set_bit(s: Ghost<Seq<USize>>, w: u64, i: usize, m: usize) {
        if m > 0 {
            ones_set_bit(s, w, i, m - 1);
            set_bit_at(s, w, i, m - 1);
        }
    }

    /// The bits to come (`bit_to_come`) among the first `m` bits, as `ones` counts the set bits.
    #[thrust_macros::logic]
    #[thrust::opaque]
    #[thrust_macros::variant(m)]
    pub(crate) fn ones_to_come(words: Seq<USize>, pos: USize, word: USize, m: USize) -> Int {
        if m <= 0 {
            0
        } else {
            ones_to_come(words, pos, word, m - 1) + bit_to_come(words, pos, word, m - 1)
        }
    }

    /// Before the first word is read, the bits to come are counted as `ones` counts the words'.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::ensures(ones_to_come(s, int_lit(0), int_lit(0), m) == ones(s, m))]
    pub(crate) fn ones_to_come_at_start(s: Ghost<Seq<USize>>, m: usize) {
        if m > 0 {
            ones_to_come_at_start(s, m - 1);
            bit_to_come_at_start(s, m - 1);
        }
    }

    /// `ones_to_come` counts at most the bits it reads.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::ensures(0 <= ones_to_come(s, pos, w, m) && ones_to_come(s, pos, w, m) <= m)]
    pub(crate) fn ones_to_come_le(s: Ghost<Seq<USize>>, pos: usize, w: u64, m: usize) {
        if m > 0 {
            ones_to_come_le(s, pos, w, m - 1);
            bit_to_come_range(s, pos, w, m - 1);
        }
    }

    /// `bit_to_come_next_word` over the first `m` bits.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::requires(0 < pos && pos <= s.len() && m <= 64 * s.len())]
    #[thrust_macros::ensures(ones_to_come(s, pos, s[pos - 1], m) == ones_to_come(s, pos - 1, int_lit(0), m))]
    pub(crate) fn ones_to_come_next_word(s: Ghost<Seq<USize>>, pos: usize, m: usize) {
        if m > 0 {
            ones_to_come_next_word(s, pos, m - 1);
            bit_to_come_next_word(s, pos, m - 1);
        }
    }

    /// `bit_to_come_clear` over the first `m` bits: one fewer to come when they hold the bit
    /// cleared.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::requires(0 < pos && pos <= s.len() && m <= 64 * s.len())]
    #[thrust_macros::requires(0 <= w && w <= 18446744073709551615u64 && w != 0 && 0 <= b && b <= 64)]
    #[thrust_macros::requires((b == 64) == (BitVec::<64, false>::from_int(w) == BitVec::from_int(0)))]
    #[thrust_macros::requires((b != 64)
        == ((BitVec::<64, false>::from_int(w) << BitVec::from_int(63 - b))
            == (BitVec::<64, false>::from_int(1) << BitVec::from_int(63))))]
    #[thrust_macros::requires(v == (BitVec::<64, false>::from_int(w)
        ^ BitVec::from_int((BitVec::<64, false>::from_int(1) << (BitVec::from_int(b) & BitVec::from_int(63))).to_int()))
        .to_int())]
    #[thrust_macros::ensures(64 * (pos - 1) + b < m ==> ones_to_come(s, pos, v, m) + 1 == ones_to_come(s, pos, w, m))]
    #[thrust_macros::ensures(m <= 64 * (pos - 1) + b ==> ones_to_come(s, pos, v, m) == ones_to_come(s, pos, w, m))]
    pub(crate) fn ones_to_come_clear(s: Ghost<Seq<USize>>, pos: usize, w: Ghost<USize>, b: usize, v: u64, m: usize) {
        if m > 0 {
            ones_to_come_clear(s, pos, w, b, v, m - 1);
            bit_to_come_clear(s, pos, w, b, v, m - 1);
        }
    }

    /// `bit_to_come_exhausted` over the first `m` bits.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::requires(m <= 64 * s.len())]
    #[thrust_macros::ensures(s.len() <= pos ==> ones_to_come(s, pos, int_lit(0), m) == 0)]
    pub(crate) fn ones_to_come_exhausted(s: Ghost<Seq<USize>>, pos: usize, m: usize) {
        if m > 0 {
            ones_to_come_exhausted(s, pos, m - 1);
            bit_to_come_exhausted(s, pos, m - 1);
        }
    }

    /// With the bits from `n` up to `m` clear, `ones` counts as many among the first `m` bits as
    /// among the first `n`.
    #[thrust::reveal]
    #[thrust_macros::lemma]
    #[thrust_macros::variant(m)]
    #[thrust_macros::requires(forall(|p: USize| !(n <= p && p < m) || bit(s, p) == 0))]
    #[thrust_macros::ensures(0 <= n && n <= m ==> ones(s, m) == ones(s, n))]
    pub(crate) fn ones_past(s: Ghost<Seq<USize>>, n: Ghost<USize>, m: usize) {
        if m > 0 {
            ones_past(s, n, m - 1);
        }
    }
}

/// Words of all ones, the excess bits past `n` then cleared, have every bit below `n` set, by
/// `full_word_bits` and `low_mask_bits` at `t`, which the caller states.
#[thrust_macros::lemma]
#[thrust_macros::requires(s.len() == (n + 63) / 64)]
#[thrust_macros::requires(forall(|k: USize| 0 <= k && k < s.len() ==> s[k] == 18446744073709551615u64))]
#[thrust_macros::requires(excess_cleared(s, n, t))]
#[thrust_macros::requires(forall(|p: USize| 0 <= p && t[p / 64] == 18446744073709551615u64 ==> bit(t, p) == 1))]
#[thrust_macros::requires(forall(|p: USize| 0 <= p && p % 64 < n % 64
    && t[p / 64] == masked(s[s.len() - 1], n)
    ==> bit(t, p) == 1))]
#[thrust_macros::ensures(forall(|p: USize| 0 <= p && p < n ==> bit(t, p) == 1))]
fn filled_bits(s: Ghost<Seq<USize>>, n: usize, t: Ghost<Seq<USize>>) {}

/// Words of all ones, the excess bits past `n` then cleared, have no bit set at or past `n`, by
/// `high_mask_bits` at `t` and `x`, the word of all ones, which the caller states.
#[thrust_macros::lemma]
#[thrust_macros::requires(x == 18446744073709551615u64)]
#[thrust_macros::requires(s.len() == (n + 63) / 64)]
#[thrust_macros::requires(forall(|k: USize| 0 <= k && k < s.len() ==> s[k] == 18446744073709551615u64))]
#[thrust_macros::requires(excess_cleared(s, n, t))]
#[thrust_macros::requires(forall(|p: USize| 0 <= p && n % 64 <= p % 64 && t[p / 64] == masked(x, n)
    ==> bit(t, p) == 0))]
#[thrust_macros::ensures(forall(|p: USize| !(n <= p && p < 64 * t.len()) || bit(t, p) == 0))]
fn excess_bits_clear(s: Ghost<Seq<USize>>, x: u64, n: usize, t: Ghost<Seq<USize>>) {}

#[inline]
#[thrust::callable]
fn count_ones(words: &[Word]) -> usize {
    words.iter().map(|word| word.count_ones() as usize).sum()
}
