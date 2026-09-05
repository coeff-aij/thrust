//@ignore-on-host: work in progress, not yet verifiable
//@edition: 2024
#![feature(new_range_api)]
// Adapted from rust-lang/rust
// commit: 89a99936d9e76a50e8df622e7242190841fd871b
// Licensed under MIT OR Apache-2.0

// //== ./../rustc_hashes/src/lib.rs

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Hash64 {
    inner: u64,
}

// Written out instead of `#[derive(Default)]`; same value.
impl Default for Hash64 {
    fn default() -> Self {
        Hash64 { inner: 0 }
    }
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

// //== ./../rustc_index/src/bit_set.rs

type Word = u64;
const WORD_BYTES: usize = size_of::<Word>();
const WORD_BITS: usize = WORD_BYTES * 8;

// #[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
#[derive(Eq)]
pub struct DenseBitSet<T> {
    domain_size: usize,
    words: Vec<Word>,
    marker: PhantomData<T>,
}

// Written out instead of `#[derive(PartialEq)]`; see the note on IndexVec.
impl<T> PartialEq for DenseBitSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.domain_size == other.domain_size && self.words == other.words
    }
}

impl<T: Idx> DenseBitSet<T> {
    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
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
    #[thrust::callable]
    pub fn contains(&self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let (word_index, mask) = word_index_and_mask(elem);
        (self.words[word_index] & mask) != 0
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
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
    #[thrust::callable]
    pub fn insert_all(&mut self) {
        self.words.fill(!0);
        self.clear_excess_bits();
    }

    #[inline]
    pub fn iter(&self) -> BitIter<'_, T> {
        BitIter::new(&self.words)
    }
}

pub struct BitIter<'a, T: Idx> {
    word: Word,

    offset: usize,

    // Position-based replacement for `slice::Iter<'a, Word>`, whose raw
    // pointer fields have no model in Thrust.
    words: &'a [Word],
    pos: usize,

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
            words,
            pos: 0,
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

            if self.pos >= self.words.len() {
                return None;
            }
            self.word = self.words[self.pos];
            self.pos += 1;
            self.offset = self.offset.wrapping_add(WORD_BITS);
        }
    }
}

// #[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
#[derive(Eq)]
pub struct BitMatrix<R: Idx, C: Idx> {
    num_rows: usize,
    num_columns: usize,
    words: Vec<Word>,
    marker: PhantomData<(R, C)>,
}

// Written out instead of `#[derive(Clone)]`; see the note on IndexVec.
impl<R: Idx, C: Idx> Clone for BitMatrix<R, C> {
    fn clone(&self) -> Self {
        BitMatrix {
            num_rows: self.num_rows,
            num_columns: self.num_columns,
            words: self.words.clone(),
            marker: PhantomData,
        }
    }
}

// Written out instead of `#[derive(PartialEq)]`; see the note on IndexVec.
impl<R: Idx, C: Idx> PartialEq for BitMatrix<R, C> {
    fn eq(&self, other: &Self) -> bool {
        self.num_rows == other.num_rows
            && self.num_columns == other.num_columns
            && self.words == other.words
    }
}

impl<R: Idx, C: Idx> BitMatrix<R, C> {
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
    #[thrust::callable]
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
use std::fmt::Debug;
use std::hash::Hash;

pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    fn new(idx: usize) -> Self;

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

impl Idx for usize {
    #[inline]
    fn new(idx: usize) -> Self {
        idx
    }
    #[inline]
    fn index(self) -> usize {
        self
    }
}

impl Idx for u32 {
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

// //== ./../rustc_index/src/slice.rs

use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

// The original is a `#[repr(transparent)]` DST wrapping `[T]`, reached through
// an unsafe pointer cast from `&[T]`. Thrust has no model for unsized struct
// fields and generic slices are not modeled yet, so the view holds a reference
// to the backing Vec (every IndexSlice here comes from an IndexVec); `&IndexSlice<I, T>`
// in the original corresponds to `IndexSlice<'_, I, T>` here. Mutation goes
// through IndexVec directly (the only place it happened in this code).
#[derive(Eq)]
pub struct IndexSlice<'a, I: Idx, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: &'a Vec<T>,
}

// Written out instead of `#[derive(PartialEq)]`; see the note on IndexVec.
impl<'a, I: Idx, T: PartialEq> PartialEq for IndexSlice<'a, I, T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<'a, I: Idx, T> Clone for IndexSlice<'a, I, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, I: Idx, T> Copy for IndexSlice<'a, I, T> {}

/// Own iterator standing in for `slice::Iter<'a, T>` (whose raw pointer
/// fields have no model in Thrust): yields `&raw[0]`, ..., `&raw[len - 1]`.
pub struct SliceIter<'a, T> {
    raw: &'a Vec<T>,
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
    raw: &'a Vec<T>,
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

impl<'a, I: Idx, T> IndexSlice<'a, I, T> {
    #[inline]
    pub const fn from_raw(raw: &'a Vec<T>) -> Self {
        IndexSlice {
            _marker: PhantomData,
            raw,
        }
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
    pub fn iter(&self) -> SliceIter<'a, T> {
        SliceIter {
            raw: self.raw,
            pos: 0,
        }
    }

    #[inline]
    pub fn iter_enumerated(&self) -> IterEnumerated<'a, I, T> {
        let _ = I::new(self.len());
        IterEnumerated {
            raw: self.raw,
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

impl<'a, I: Idx, J: Idx> IndexSlice<'a, I, J> {
    pub fn invert_bijective_mapping(&self) -> IndexVec<J, I> {
        debug_assert_eq!(
            self.iter().map(|x| x.index() as u128).sum::<u128>(),
            (0..self.len() as u128).sum::<u128>(),
            // "The values aren't 0..N in input {self:?}",
        );

        let mut inverse = IndexVec::from_elem_n(Idx::new(0), self.len());
        let mut entries = self.iter_enumerated();
        while let Some((i1, &i2)) = entries.next() {
            inverse[i2] = i1;
        }

        debug_assert_eq!(
            inverse.iter().map(|x| x.index() as u128).sum::<u128>(),
            (0..inverse.len() as u128).sum::<u128>(),
            // "The values aren't 0..N in result {self:?}",
        );

        inverse
    }
}

// The original goes through `IntoSliceIdx<I, [T]>`, whose only impl used
// here maps `I: Idx` to `usize`; this is that instance written out.
impl<'a, I: Idx, T> Index<I> for IndexSlice<'a, I, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: I) -> &T {
        &self.raw[index.index()]
    }
}

// //== ./../rustc_index/src/vec.rs

use std::ops::Deref;

#[derive(Eq)]
#[repr(transparent)]
pub struct IndexVec<I: Idx, T> {
    pub raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

// Written out instead of `#[derive(Clone)]`: the derived impl also clones the
// PhantomData field through the generic Clone::clone spec, which cannot bind
// unit-modeled arguments (same limitation as for PartialEq below).
impl<I: Idx, T: Clone> Clone for IndexVec<I, T> {
    fn clone(&self) -> Self {
        IndexVec {
            raw: self.raw.clone(),
            _marker: PhantomData,
        }
    }
}

// Written out instead of `#[derive(PartialEq)]`: the derived impl also
// compares the PhantomData field, which Thrust's generic PartialEq::eq spec
// cannot bind (unit-modeled arguments). PhantomData values are always equal,
// so this is the same relation.
impl<I: Idx, T: PartialEq> PartialEq for IndexVec<I, T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

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
    pub fn from_elem<S>(elem: T, universe: IndexSlice<'_, I, S>) -> Self
    where
        T: Clone,
    {
        IndexVec::from_raw(vec![elem; universe.len()])
    }

    #[inline]
    pub fn from_elem_n(elem: T, n: usize) -> Self
    where
        T: Clone,
    {
        IndexVec::from_raw(vec![elem; n])
    }

    #[inline]
    pub fn as_slice(&self) -> IndexSlice<'_, I, T> {
        IndexSlice::from_raw(&self.raw)
    }

    #[inline]
    pub fn push(&mut self, d: T) -> I {
        let idx = self.next_index();
        self.raw.push(d);
        idx
    }

    // The original reaches the following through `Deref<Target = IndexSlice>`;
    // with IndexSlice a by-value view, spell the deref-then-call out.

    #[inline]
    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    #[inline]
    pub fn next_index(&self) -> I {
        self.as_slice().next_index()
    }

    #[inline]
    pub fn iter(&self) -> SliceIter<'_, T> {
        self.as_slice().iter()
    }

    #[inline]
    pub fn iter_enumerated(&self) -> IterEnumerated<'_, I, T> {
        self.as_slice().iter_enumerated()
    }
}

impl<I: Idx, J: Idx> IndexVec<I, J> {
    pub fn invert_bijective_mapping(&self) -> IndexVec<J, I> {
        self.as_slice().invert_bijective_mapping()
    }
}

impl<I: Idx, T> Index<I> for IndexVec<I, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: I) -> &T {
        &self.raw[index.index()]
    }
}

impl<I: Idx, T> IndexMut<I> for IndexVec<I, T> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut T {
        &mut self.raw[index.index()]
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

// //== ./src/layout/coroutine.rs

#[derive(Clone, /*Debug,*/ PartialEq)]
enum SavedLocalEligibility<VariantIdx, FieldIdx> {
    Unassigned,
    Assigned(VariantIdx),
    Ineligible(Option<FieldIdx>),
}

fn coroutine_saved_local_eligibility<VariantIdx: Idx, FieldIdx: Idx, LocalIdx: Idx>(
    nb_locals: usize,
    variant_fields: IndexSlice<'_, VariantIdx, IndexVec<FieldIdx, LocalIdx>>,
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
        let mut locals = fields.iter();
        while let Some(local) = locals.next() {
            match assignments[*local] {
                Unassigned => {
                    assignments[*local] = Assigned(variant_index);
                }
                Assigned(idx) => {
                    // trace!(
                    //     "removing local {:?} in >1 variant ({:?}, {:?})",
                    //     local, variant_index, idx
                    // );
                    ineligible_locals.insert(*local);
                    assignments[*local] = Ineligible(None);
                }
                Ineligible(_) => {}
            }
        }
    }

    let mut rows = storage_conflicts.rows();
    while let Some(local_a) = rows.next() {
        let conflicts_a = storage_conflicts.count(local_a);
        if ineligible_locals.contains(local_a) {
            continue;
        }

        let mut conflicts = storage_conflicts.iter(local_a);
        while let Some(local_b) = conflicts.next() {
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
            // trace!(
            //     "removing local {:?} due to conflict with {:?}",
            //     remove, other
            // );
        }
    }

    {
        let mut used_variants = DenseBitSet::new_empty(variant_fields.len());
        let mut assignments_iter = assignments.iter();
        while let Some(assignment) = assignments_iter.next() {
            if let Assigned(idx) = assignment {
                used_variants.insert(*idx);
            }
        }
        if used_variants.count() < 2 {
            let mut i = 0;
            while i < assignments.len() {
                assignments.raw[i] = Ineligible(None);
                i += 1;
            }
            ineligible_locals.insert_all();
        }
    }

    {
        // `for (idx, local) in ineligible_locals.iter().enumerate()` with the
        // enumeration counter kept by hand.
        let mut ineligible = ineligible_locals.iter();
        let mut idx = 0;
        while let Some(local) = ineligible.next() {
            assignments[local] = Ineligible(Some(FieldIdx::new(idx)));
            idx += 1;
        }
    }
    // debug!("coroutine saved local assignments: {:?}", assignments);

    (ineligible_locals, assignments)
}

pub fn layout<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy,
    VariantIdx: Idx,
    FieldIdx: Idx,
    LocalIdx: Idx,
>(
    calc: &LayoutCalculator<impl HasDataLayout>,
    local_layouts: IndexSlice<'_, LocalIdx, F>,
    mut prefix_layouts: IndexVec<FieldIdx, F>,
    variant_fields: IndexSlice<'_, VariantIdx, IndexVec<FieldIdx, LocalIdx>>,
    storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>,
    tag_to_layout: impl Fn(Scalar) -> F,
) -> LayoutCalculatorResult<FieldIdx, VariantIdx, F> {
    use SavedLocalEligibility::*;

    let (ineligible_locals, assignments) =
        coroutine_saved_local_eligibility(local_layouts.len(), variant_fields, storage_conflicts);

    let tag_index = prefix_layouts.next_index();

    let max_discr = (variant_fields.len() - 1) as u128;
    let discr_int = Integer::fit_unsigned(max_discr);
    let tag = Scalar::Initialized {
        value: Primitive::Int(discr_int, false),
        valid_range: WrappingRange {
            start: 0,
            end: max_discr,
        },
    };

    // `prefix_layouts.extend(ineligible_locals.iter().map(|local| local_layouts[local]))`
    // written as the loop it performs; the lazy map ran after the tag push, as here.
    let mut promoted_locals = ineligible_locals.iter();
    prefix_layouts.push(tag_to_layout(tag));
    while let Some(local) = promoted_locals.next() {
        prefix_layouts.raw.push(local_layouts[local]);
    }
    // `?` written out (same error type, so its From conversion is the identity)
    let prefix = match calc.univariant(
        prefix_layouts.as_slice(),
        &ReprOptions::default(),
        StructKind::AlwaysSized,
    ) {
        Ok(prefix) => prefix,
        Err(err) => return Err(err),
    };

    let (prefix_size, prefix_align) = (prefix.size, prefix.align);

    // debug!("prefix = {:#?}", prefix);
    let (outer_fields, promoted_offsets, promoted_memory_index) = match prefix.fields {
        FieldsShape::Arbitrary {
            mut offsets,
            in_memory_order,
        } => {
            let b_start = tag_index.plus(1);
            let offsets_b = IndexVec::from_raw(offsets.raw.split_off(b_start.index()));
            let offsets_a = offsets;

            let mut in_memory_order_a = IndexVec::<u32, FieldIdx>::new();
            let mut in_memory_order_b = IndexVec::<u32, FieldIdx>::new();
            let mut in_memory_order_iter = in_memory_order.iter();
            while let Some(&i) = in_memory_order_iter.next() {
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
                in_memory_order_b.invert_bijective_mapping(),
            )
        }
        _ => unreachable!(),
    };

    let mut size = prefix.size;
    let mut align = prefix.align;
    // Originally `variant_fields.iter_enumerated().map(|(index, variant_fields)| { .. })
    //     .collect::<Result<IndexVec<VariantIdx, _>, _>>()?`:
    // each Ok is pushed, the first Err is returned from layout().
    let mut variants: IndexVec<VariantIdx, VariantLayout<FieldIdx>> = IndexVec::new();
    let mut variant_entries = variant_fields.iter_enumerated();
    while let Some((index, variant_fields)) = variant_entries.next() {
        // Originally `variant_fields.iter().filter(|local| match ..).map(|local| local_layouts[*local])
        //     .collect::<IndexVec<_, _>>()`.
        let mut variant_only_tys: IndexVec<FieldIdx, F> = IndexVec::new();
        let mut variant_locals = variant_fields.iter();
        while let Some(local) = variant_locals.next() {
            let keep = match assignments[*local] {
                Unassigned => unreachable!(),
                Assigned(v) if v == index => true,
                // message dropped: format arguments are not modeled
                Assigned(_) => unreachable!(),
                Ineligible(_) => false,
            };
            if keep {
                variant_only_tys.raw.push(local_layouts[*local]);
            }
        }

        // `?` written out (same error type, so its From conversion is the identity)
        let mut variant = match calc.univariant(
            variant_only_tys.as_slice(),
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
            unreachable!();
        };

        let memory_index = in_memory_order.invert_bijective_mapping();
        let invalid_field_idx = promoted_memory_index.len() + memory_index.len();
        let mut combined_in_memory_order =
            IndexVec::from_elem_n(FieldIdx::new(invalid_field_idx), invalid_field_idx);

        let mut offsets_iter = offsets.iter();
        let mut memory_index_iter = memory_index.iter();
        // Originally `variant_fields.iter_enumerated().map(|(i, local)| { .. }).collect()`.
        let mut combined_offsets: IndexVec<FieldIdx, Size> = IndexVec::new();
        let mut field_entries = variant_fields.iter_enumerated();
        while let Some((i, local)) = field_entries.next() {
            let (offset, memory_index) = match assignments[*local] {
                Unassigned => unreachable!(),
                Assigned(_) => {
                    let offset = *offsets_iter.next().unwrap();
                    let memory_index = *memory_index_iter.next().unwrap();
                    (offset, promoted_memory_index.len() as u32 + memory_index)
                }
                Ineligible(field_idx) => {
                    let field_idx = field_idx.unwrap();
                    (
                        promoted_offsets[field_idx],
                        promoted_memory_index[field_idx],
                    )
                }
            };
            combined_in_memory_order[memory_index] = i;
            combined_offsets.raw.push(offset);
        }

        // `combined_in_memory_order.raw.retain(|&i| i.index() != invalid_field_idx)`
        // written as the filtering copy it performs (order preserved).
        let mut retained: IndexVec<u32, FieldIdx> = IndexVec::new();
        let mut combined_iter = combined_in_memory_order.iter();
        while let Some(&i) = combined_iter.next() {
            if i.index() != invalid_field_idx {
                retained.raw.push(i);
            }
        }
        let combined_in_memory_order = retained;

        variant.fields = FieldsShape::Arbitrary {
            offsets: combined_offsets,
            in_memory_order: combined_in_memory_order,
        };

        size = size.max(variant.size);
        align = align.max(variant.align);
        variants.raw.push(VariantLayout::from_layout(variant));
    }

    size = size.align_to(align.abi);

    // `variants.iter().all(|v| v.is_uninhabited())` as a short-circuiting loop,
    // still only evaluated when `prefix.uninhabited` is false.
    let uninhabited = prefix.uninhabited || {
        let mut all_variants_uninhabited = true;
        let mut variants_iter = variants.iter();
        while let Some(v) = variants_iter.next() {
            if !v.is_uninhabited() {
                all_variants_uninhabited = false;
                break;
            }
        }
        all_variants_uninhabited
    };
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

// //== ./src/layout/simple.rs

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
                offsets: IndexVec::from_raw(vec![Size::ZERO, b_offset]),
                in_memory_order: IndexVec::from_raw(vec![FieldIdx::new(0), FieldIdx::new(1)]),
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

// //== ./src/layout.rs

use std::cmp;

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

impl<Cx: HasDataLayout> LayoutCalculator<Cx> {
    #[thrust::trusted]
    #[thrust::callable]
    pub fn univariant<
        'a,
        FieldIdx: Idx,
        VariantIdx: Idx,
        F: Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + /*fmt::Debug +*/ Copy,
    >(
        &self,
        fields: IndexSlice<'_, FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
    ) -> LayoutCalculatorResult<FieldIdx, VariantIdx, F> {
        let dl = self.cx.data_layout();
        let layout = self.univariant_biased(fields, repr, kind, NicheBias::Start);

        if let Ok(layout) = &layout {
            if !matches!(kind, StructKind::MaybeUnsized) {
                if let Some(niche) = layout.largest_niche {
                    let head_space = niche.offset.bytes();
                    let niche_len = niche.value.size(dl).bytes();
                    let tail_space = layout.size.bytes() - head_space - niche_len;

                    if fields.len() > 1 && head_space != 0 && tail_space > 0 {
                        let alt_layout = self
                            .univariant_biased(fields, repr, kind, NicheBias::End)
                            // .expect("alt layout should always work");
                            .unwrap_without_debug();
                        let alt_niche = alt_layout
                            .largest_niche
                            // .expect("alt layout should have a niche like the regular one");
                            .unwrap_without_debug();
                        let alt_head_space = alt_niche.offset.bytes();
                        let alt_niche_len = alt_niche.value.size(dl).bytes();
                        let alt_tail_space =
                            alt_layout.size.bytes() - alt_head_space - alt_niche_len;

                        debug_assert_eq!(layout.size.bytes(), alt_layout.size.bytes());

                        let prefer_alt_layout =
                            alt_head_space > head_space && alt_head_space > tail_space;

                        // debug!(
                        //     "sz: {}, default_niche_at: {}+{}, default_tail_space: {}, alt_niche_at/head_space: {}+{}, alt_tail: {}, num_fields: {}, better: {}\n\
                        //     layout: {}\n\
                        //     alt_layout: {}\n",
                        //     layout.size.bytes(),
                        //     head_space,
                        //     niche_len,
                        //     tail_space,
                        //     alt_head_space,
                        //     alt_niche_len,
                        //     alt_tail_space,
                        //     layout.fields.count(),
                        //     prefer_alt_layout,
                        //     self.format_field_niches(layout, fields),
                        //     self.format_field_niches(&alt_layout, fields),
                        // );

                        if prefer_alt_layout {
                            return Ok(alt_layout);
                        }
                    }
                }
            }
        }
        layout
    }

    #[thrust::trusted]
    #[thrust::callable]
    fn univariant_biased<
        'a,
        FieldIdx: Idx,
        VariantIdx: Idx,
        F: Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + /*fmt::Debug +*/ Copy,
    >(
        &self,
        fields: IndexSlice<'_, FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
        niche_bias: NicheBias,
    ) -> LayoutCalculatorResult<FieldIdx, VariantIdx, F> {
        let dl = self.cx.data_layout();
        let pack = repr.pack;
        let mut align = if pack.is_some() {
            dl.i8_align
        } else {
            dl.aggregate_align
        };
        let mut max_repr_align = repr.align;
        let mut in_memory_order: IndexVec<u32, FieldIdx> = IndexVec::from_raw(fields.indices().collect());
        let optimize_field_order = !repr.inhibit_struct_field_reordering();
        let end = if let StructKind::MaybeUnsized = kind {
            fields.len() - 1
        } else {
            fields.len()
        };
        let optimizing = &mut in_memory_order.raw[..end];
        let fields_excluding_tail = &fields.raw[..end];

        let field_seed = fields_excluding_tail.iter().fold(Hash64::ZERO, |acc, f| {
            acc.wrapping_add(f.randomization_seed)
        });

        if optimize_field_order && fields.len() > 1 {
            if repr.can_randomize_type_layout() && cfg!(feature = "randomize") {
                #[cfg(feature = "randomize")]
                {
                    use rand::SeedableRng;
                    use rand::seq::SliceRandom;

                    let mut rng = rand_xoshiro::Xoshiro128StarStar::seed_from_u64(
                        field_seed.wrapping_add(repr.field_shuffle_seed).as_u64(),
                    );

                    optimizing.shuffle(&mut rng);
                }
            } else {
                let max_field_align = fields_excluding_tail
                    .iter()
                    .map(|f| f.align.bytes())
                    .max()
                    .unwrap_or(1);
                let largest_niche_size = fields_excluding_tail
                    .iter()
                    .filter_map(|f| f.largest_niche)
                    .map(|n| n.available(dl))
                    .max()
                    .unwrap_or(0);

                let alignment_group_key = |layout: &F| {
                    if let Some(pack) = pack {
                        layout.align.abi.min(pack).bytes()
                    } else {
                        let align = layout.align.bytes();
                        let size = layout.size.bytes();
                        let niche_size = layout.largest_niche.map(|n| n.available(dl)).unwrap_or(0);

                        let size_as_align = align.max(size).trailing_zeros();
                        let size_as_align = if largest_niche_size > 0 {
                            match niche_bias {
                                NicheBias::Start => {
                                    max_field_align.trailing_zeros().min(size_as_align)
                                }

                                NicheBias::End if niche_size == largest_niche_size => {
                                    align.trailing_zeros()
                                }
                                NicheBias::End => size_as_align,
                            }
                        } else {
                            size_as_align
                        };
                        size_as_align as u64
                    }
                };

                match kind {
                    StructKind::AlwaysSized | StructKind::MaybeUnsized => {
                        optimizing.sort_by_key(|&x| {
                            let f = &fields[x];
                            let field_size = f.size.bytes();
                            let niche_size = f.largest_niche.map_or(0, |n| n.available(dl));
                            let niche_size_key = match niche_bias {
                                NicheBias::Start => !niche_size,

                                NicheBias::End => niche_size,
                            };
                            let inner_niche_offset_key = match niche_bias {
                                NicheBias::Start => f.largest_niche.map_or(0, |n| n.offset.bytes()),
                                NicheBias::End => f.largest_niche.map_or(0, |n| {
                                    !(field_size - n.value.size(dl).bytes() - n.offset.bytes())
                                }),
                            };

                            (
                                cmp::Reverse(alignment_group_key(f)),
                                niche_size_key,
                                inner_niche_offset_key,
                            )
                        });
                    }

                    StructKind::Prefixed(..) => {
                        optimizing.sort_by_key(|&x| {
                            let f = &fields[x];
                            let niche_size = f.largest_niche.map_or(0, |n| n.available(dl));
                            (alignment_group_key(f), niche_size)
                        });
                    }
                }
            }
        }

        let mut unsized_field = None::<&F>;
        let mut offsets = IndexVec::from_elem(Size::ZERO, fields);
        let mut offset = Size::ZERO;
        let mut largest_niche = None;
        let mut largest_niche_available = 0;
        if let StructKind::Prefixed(prefix_size, prefix_align) = kind {
            let prefix_align = if let Some(pack) = pack {
                prefix_align.min(pack)
            } else {
                prefix_align
            };
            align = align.max(prefix_align);
            offset = prefix_size.align_to(prefix_align);
        }
        for &i in &in_memory_order {
            let field = &fields[i];
            if let Some(unsized_field) = unsized_field {
                return Err(LayoutCalculatorError::UnexpectedUnsized(*unsized_field));
            }

            if field.is_unsized() {
                if let StructKind::MaybeUnsized = kind {
                    unsized_field = Some(field);
                } else {
                    return Err(LayoutCalculatorError::UnexpectedUnsized(*field));
                }
            }

            let field_align = if let Some(pack) = pack {
                field.align.min(AbiAlign::new(pack))
            } else {
                field.align
            };
            offset = offset.align_to(field_align.abi);
            align = align.max(field_align.abi);
            max_repr_align = max_repr_align.max(field.max_repr_align);

            // debug!("univariant offset: {:?} field: {:#?}", offset, field);
            offsets[i] = offset;

            if let Some(mut niche) = field.largest_niche {
                let available = niche.available(dl);

                let prefer_new_niche = match niche_bias {
                    NicheBias::Start => available > largest_niche_available,

                    NicheBias::End => available >= largest_niche_available,
                };
                if prefer_new_niche {
                    largest_niche_available = available;
                    niche.offset += offset;
                    largest_niche = Some(niche);
                }
            }

            offset = offset
                .checked_add(field.size, dl)
                .ok_or(LayoutCalculatorError::SizeOverflow)?;
        }

        let unadjusted_abi_align = align;
        if let Some(repr_align) = repr.align {
            align = align.max(repr_align);
        }

        let align = align;

        // debug!("univariant min_size: {:?}", offset);
        let min_size = offset;
        let size = min_size.align_to(align);

        if size.bytes() >= dl.obj_size_bound() {
            return Err(LayoutCalculatorError::SizeOverflow);
        }
        let mut layout_of_single_non_zst_field = None;
        let sized = unsized_field.is_none();
        let mut abi = BackendRepr::Memory { sized };

        let optimize_abi = !repr.inhibit_newtype_abi_optimization();

        if sized && size.bytes() > 0 {
            let mut non_zst_fields = fields.iter_enumerated().filter(|&(_, f)| !f.is_zst());

            match (
                non_zst_fields.next(),
                non_zst_fields.next(),
                non_zst_fields.next(),
            ) {
                (Some((i, field)), None, None) => {
                    layout_of_single_non_zst_field = Some(field);

                    if offsets[i].bytes() == 0 && align == field.align.abi && size == field.size {
                        match field.backend_repr {
                            BackendRepr::Scalar(_) | BackendRepr::SimdVector { .. }
                                if optimize_abi =>
                            {
                                abi = field.backend_repr;
                            }

                            BackendRepr::ScalarPair(..) => {
                                abi = field.backend_repr;
                            }
                            _ => {}
                        }
                    }
                }

                (Some((i, a)), Some((j, b)), None) => match (a.backend_repr, b.backend_repr) {
                    (BackendRepr::Scalar(a), BackendRepr::Scalar(b)) => {
                        let ((i, a), (j, b)) = if offsets[i] < offsets[j] {
                            ((i, a), (j, b))
                        } else {
                            ((j, b), (i, a))
                        };
                        let pair = LayoutData::<FieldIdx, VariantIdx>::scalar_pair(&self.cx, a, b);
                        let pair_offsets = match pair.fields {
                            FieldsShape::Arbitrary {
                                ref offsets,
                                ref in_memory_order,
                            } => {
                                assert_eq!(
                                    in_memory_order.raw,
                                    [FieldIdx::new(0), FieldIdx::new(1)]
                                );
                                offsets
                            }
                            FieldsShape::Primitive
                            | FieldsShape::Array { .. }
                            | FieldsShape::Union(..) => {
                                panic!("encountered a non-arbitrary layout during enum layout")
                            }
                        };
                        if offsets[i] == pair_offsets[FieldIdx::new(0)]
                            && offsets[j] == pair_offsets[FieldIdx::new(1)]
                            && align == pair.align.abi
                            && size == pair.size
                        {
                            abi = pair.backend_repr;
                        }
                    }
                    _ => {}
                },

                _ => {}
            }
        }
        let uninhabited = fields.iter().any(|f| f.is_uninhabited());

        let unadjusted_abi_align = if repr.transparent() {
            match layout_of_single_non_zst_field {
                Some(l) => l.unadjusted_abi_align,
                None => align,
            }
        } else {
            unadjusted_abi_align
        };

        let seed = field_seed.wrapping_add(repr.field_shuffle_seed);

        Ok(LayoutData {
            variants: Variants::Single {
                index: VariantIdx::new(0),
            },
            fields: FieldsShape::Arbitrary {
                offsets,
                in_memory_order,
            },
            backend_repr: abi,
            largest_niche,
            uninhabited,
            align: AbiAlign::new(align),
            size,
            max_repr_align,
            unadjusted_abi_align,
            randomization_seed: seed,
        })
    }
}

// //== ./src/lib.rs

// #![cfg_attr(feature = "nightly", allow(internal_features))]
// #![cfg_attr(feature = "nightly", feature(rustc_attrs))]
// #![cfg_attr(feature = "nightly", feature(step_trait))]

use std::num::NonZeroUsize;
use std::ops::{Add, AddAssign};
use std::range::RangeInclusive;

#[derive(Clone, Copy, PartialEq, Eq)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct ReprFlags(u8);

// Written out instead of `#[derive(Default)]`; same value.
impl Default for ReprFlags {
    fn default() -> Self {
        ReprFlags(0)
    }
}

// Hand-written replacement for the `bitflags!` invocation in rustc_abi, since
// external crates are not available under ui_test.
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

    pub const fn contains(&self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    pub const fn intersects(&self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

#[derive(Copy, Clone, /*Debug,*/ Eq, PartialEq)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub enum IntegerType {
    Pointer(bool),

    Fixed(Integer, bool),
}

#[derive(Copy, Clone, /*Debug,*/ Eq, PartialEq)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub enum ScalableElt {
    ElementCount(u16),

    Container,
}

#[derive(Copy, Clone, /*Debug,*/ Eq, PartialEq)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct ReprOptions {
    pub int: Option<IntegerType>,
    pub align: Option<Align>,
    pub pack: Option<Align>,
    pub flags: ReprFlags,

    pub scalable: Option<ScalableElt>,

    pub field_shuffle_seed: Hash64,
}

// Written out instead of `#[derive(Default)]`; same value.
impl Default for ReprOptions {
    fn default() -> Self {
        ReprOptions {
            int: None,
            align: None,
            pack: None,
            flags: ReprFlags::default(),
            scalable: None,
            field_shuffle_seed: Hash64::default(),
        }
    }
}

impl ReprOptions {
    #[inline]
    pub fn transparent(&self) -> bool {
        self.flags.contains(ReprFlags::IS_TRANSPARENT)
    }

    pub fn inhibit_newtype_abi_optimization(&self) -> bool {
        self.flags.intersects(ReprFlags::ABI_UNOPTIMIZABLE)
    }

    pub fn inhibit_struct_field_reordering(&self) -> bool {
        self.flags.intersects(ReprFlags::FIELD_ORDER_UNOPTIMIZABLE) || self.int.is_some()
    }

    pub fn can_randomize_type_layout(&self) -> bool {
        !self.inhibit_struct_field_reordering() && self.flags.contains(ReprFlags::RANDOMIZE_LAYOUT)
    }
}

#[derive(Copy, Clone, /*Debug,*/ PartialEq, Eq)]
pub struct PointerSpec {
    pointer_size: Size,

    pointer_align: Align,

    pointer_offset: Size,

    _is_fat: bool,
}

#[derive(/*Debug,*/ PartialEq, Eq)]
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

impl TargetDataLayout {
    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
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
    #[thrust::callable]
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
    #[thrust::callable]
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

#[derive(Copy, Clone, PartialEq, Eq)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct Size {
    raw: u64,
}

impl PartialOrd for Size {
    fn partial_cmp(&self, other: &Size) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// Written out instead of `#[derive(PartialOrd, Ord)]`, which would call std
// comparison functions; same ordering (by `raw`).
impl Ord for Size {
    fn cmp(&self, other: &Size) -> cmp::Ordering {
        if self.raw < other.raw {
            cmp::Ordering::Less
        } else if self.raw > other.raw {
            cmp::Ordering::Greater
        } else {
            cmp::Ordering::Equal
        }
    }

    // Same results as the defaults, without going through std's bodies.
    fn max(self, other: Size) -> Size {
        if other.raw >= self.raw {
            other
        } else {
            self
        }
    }

    fn min(self, other: Size) -> Size {
        if other.raw < self.raw {
            other
        } else {
            self
        }
    }
}

impl Size {
    pub const ZERO: Size = Size { raw: 0 };

    #[thrust::trusted]
    #[thrust::callable]
    pub fn from_bits(bits: impl TryInto<u64>) -> Size {
        let bits = bits.try_into().ok().unwrap();
        Size {
            raw: bits.div_ceil(8),
        }
    }

    // Every caller passes a u64 (or a literal), for which the original's
    // `try_into().ok().unwrap()` is the identity; the generic conversion is
    // a std call Thrust has no spec for.
    #[inline]
    pub fn from_bytes(bytes: u64) -> Size {
        Size { raw: bytes }
    }

    #[inline]
    pub fn bytes(self) -> u64 {
        self.raw
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
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

#[derive(Copy, Clone, PartialEq, Eq)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub struct Align {
    pow2: u8,
}

impl PartialOrd for Align {
    fn partial_cmp(&self, other: &Align) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// Written out instead of `#[derive(PartialOrd, Ord)]`, which would call std
// comparison functions; same ordering (by `pow2`). Still needed for
// `Option<Align>::max` in univariant_biased.
impl Ord for Align {
    fn cmp(&self, other: &Align) -> cmp::Ordering {
        if self.pow2 < other.pow2 {
            cmp::Ordering::Less
        } else if self.pow2 > other.pow2 {
            cmp::Ordering::Greater
        } else {
            cmp::Ordering::Equal
        }
    }
}

impl Align {
    // The original uses Ord::max/min; these compute the same without going
    // through std's bodies (method resolution prefers the inherent ones).
    pub fn max(self, other: Align) -> Align {
        if other.pow2 >= self.pow2 {
            other
        } else {
            self
        }
    }

    pub fn min(self, other: Align) -> Align {
        if other.pow2 < self.pow2 {
            other
        } else {
            self
        }
    }

    pub const ONE: Align = Align { pow2: 0 };
    pub const EIGHT: Align = Align { pow2: 3 };

    pub const MAX: Align = Align { pow2: 29 };

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub const fn bytes(self) -> u64 {
        1 << self.pow2
    }
}

#[derive(Copy, Clone, PartialEq, Eq /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
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

#[derive(Copy, Clone, PartialEq, Eq /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(Encodable_NoContext, Decodable_NoContext, StableHash))]
pub enum Integer {
    I8,
    I16,
    I32,
    I64,
    I128,
}

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

#[derive(Copy, Clone, PartialEq, Eq /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum Float {
    F16,
    F32,
    F64,
    F128,
}

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

#[derive(Copy, Clone, PartialEq, Eq /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum Primitive {
    Int(Integer, bool),
    Float(Float),
    Pointer(AddressSpace),
}

impl Primitive {
    pub fn size<C: HasDataLayout>(self, cx: &C) -> Size {
        use Primitive::*;
        let dl = cx.data_layout();

        match self {
            Int(i, _) => i.size(),
            Float(f) => f.size(),
            Pointer(a) => dl.pointer_size_in(a),
        }
    }

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

#[derive(Clone, Copy, PartialEq, Eq)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct WrappingRange {
    pub start: u128,
    pub end: u128,
}

#[derive(Clone, Copy, PartialEq, Eq /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
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

#[derive(PartialEq, Eq, Clone /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum FieldsShape<FieldIdx: Idx> {
    Primitive,

    Union(NonZeroUsize),

    Array {
        stride: Size,
        count: u64,
    },

    Arbitrary {
        offsets: IndexVec<FieldIdx, Size>,

        in_memory_order: IndexVec<u32, FieldIdx>,
    },
}

#[derive(Copy, Clone, /*Debug,*/ PartialEq, Eq)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct AddressSpace(pub u32);

#[derive(Clone, Copy, PartialEq, Eq /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub struct NumScalableVectors(pub u8);

#[derive(Clone, Copy, PartialEq, Eq /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
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

#[derive(PartialEq, Eq, Clone /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
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

#[derive(PartialEq, Eq, Copy, Clone /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum TagEncoding<VariantIdx: Idx> {
    Direct,

    Niche {
        untagged_variant: VariantIdx,

        niche_variants: RangeInclusive<VariantIdx>,

        niche_start: u128,
    },
}

#[derive(Clone, Copy, PartialEq, Eq /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
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

#[derive(PartialEq, Eq, Clone)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
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

#[derive(Copy, Clone /*Debug*/)]
pub enum StructKind {
    AlwaysSized,

    MaybeUnsized,

    Prefixed(Size, Align),
}

#[derive(PartialEq, Eq, Clone /*Debug*/)]
// #[cfg_attr(feature = "nightly", derive(StableHash))]
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
            // message dropped: format arguments are not modeled
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

fn main() {}

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
