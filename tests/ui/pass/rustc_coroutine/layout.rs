//@ignore-on-host: draft, blocked on generic slices and std iterator adapters (see README.md)
//@edition: 2024
#![feature(new_range_api)]
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// Extracted from tests/ui/pass/traits/rustc-coroutine.rs (rustc's
// rustc_abi::layout::coroutine::layout, adapted). Stage 7 of the
// rustc_coroutine plan (README.md, "段階 7"). Everything `layout()` needs is
// copied verbatim, mostly from the already-annotated eligibility.rs (stage 5)
// and univariant.rs (stage 6, itself sourced from values.rs stage 1) rather
// than re-derived, for the same reason those two reuse bitset.rs/values.rs.
// This file is a DRAFT: it is not expected to verify (`ignore-on-host`
// above). `layout()` itself gets the `requires` from README 段階 5/7 that
// typecheck, plus `// TODO(proof):` comments at each panic site naming the
// README fact that discharges it, plus a trusted `lemma_permutation_split`
// skeleton (not called from `layout()`, per the task).

use thrust_models::forall;
use thrust_models::model::Int;

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

impl<T: Idx> DenseBitSet<T> {
    #[thrust::trusted]
    #[thrust::callable]
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

// See univariant.rs's copy of this impl: `in_memory_order: IndexVec<u32,
// FieldIdx>` needs `u32: Idx`; trusted for the same `as`-cast reason.
#[thrust_macros::context]
impl Idx for u32 {
    #[thrust_macros::predicate]
    fn index_is(self, i: usize) -> bool {
        "(= i self_)";
        true
    }

    #[thrust_macros::predicate]
    fn can_new(idx: usize) -> bool {
        "(<= idx 4294967295)";
        true
    }

    #[thrust::trusted]
    #[thrust::callable]
    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }
    #[thrust::trusted]
    #[thrust::callable]
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

// //== ./../rustc_index/src/slice.rs (from eligibility.rs / univariant.rs)

#[derive(PartialEq, Eq, Hash)]
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

    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.raw.iter_mut()
    }
}

impl<I: Idx, J: Idx> IndexSlice<I, J> {
    // TODO(proof): `debug_assert_eq!` calls dropped (debug-assertions are
    // off, out of scope). The README's needed precondition on this
    // (`invert_bijective_mapping`'s `requires` is "all elements < len") and
    // the permutation-split lemma below are how `layout()`'s later panics
    // are meant to be discharged; not wired up yet (see the report).
    pub fn invert_bijective_mapping(&self) -> IndexVec<J, I> {
        let mut inverse = IndexVec::from_elem_n(Idx::new(0), self.len());
        let mut entries = self.iter_enumerated();
        while let Some((i1, &i2)) = entries.next() {
            inverse[i2] = i1;
        }
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

// //== ./../rustc_index/src/vec.rs (from eligibility.rs / univariant.rs)

#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexVec<I: Idx, T> {
    pub raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
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
    pub fn from_elem<S>(elem: T, universe: &IndexSlice<I, S>) -> Self
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

impl<I: Idx, T, const N: usize> From<[T; N]> for IndexVec<I, T> {
    #[inline]
    fn from(array: [T; N]) -> Self {
        IndexVec::from_raw(array.into())
    }
}

// //== ./src/layout/coroutine.rs: `coroutine_saved_local_eligibility` (from
// eligibility.rs, stage 5; `layout()` only calls it, so it keeps only the
// length/domain facts `layout()`'s own panics need, not the full stage 5
// contract -- see eligibility.rs for that).

#[derive(Clone, Debug, PartialEq)]
enum SavedLocalEligibility<VariantIdx, FieldIdx> {
    Unassigned,
    Assigned(VariantIdx),
    Ineligible(Option<FieldIdx>),
}

// Trusted stub here: this file only calls it, its full contract lives in
// eligibility.rs (stage 5).
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
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
// `requires` below covers the two README 段階 7 facts that typecheck without
// needing generic-slice element access (variant_fields non-empty; the
// storage_conflicts / variant_fields / local_layouts dimensions agreeing).
// The remaining ones -- `dl_wf`/`niche_wf` of the inputs, and the
// well-formedness of `variant_fields`/`storage_conflicts` from README 段階 5
// -- hit the same wall as `eligibility.rs`'s own `requires` (indexing through
// `IndexSlice`'s `Seq`-shaped model needs `FieldIdx`/`VariantIdx`/`LocalIdx`
// to be `Model<Ty = Int>`, unconstrained for a generic `Idx`); see that
// file's report entry, not repeated here.
// TODO(spec): tried `requires(variant_fields.length > 0 && ...)` /
// `ensures(true)` here (the two 段階 7 facts that don't need generic-slice
// element access) but it does not compile: `calc: &LayoutCalculator<impl
// HasDataLayout>` and `tag_to_layout: impl Fn(Scalar) -> F` use *anonymous*
// `impl Trait` argument types, legal for the real function but not once
// `FormulaFnTypeLowering::lower_params` re-embeds the same type inside a
// `<.. as Model>::Ty` qualified-path position for the companion function --
// `error[E0562]: impl Trait is not allowed in paths`. This reproduces
// regardless of whether the formula even mentions `calc`/`tag_to_layout`,
// and the real signature must not change (see the report): so `layout()`
// carries no `requires`/`ensures` at all in this draft.
pub fn layout<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy,
    VariantIdx: Idx,
    FieldIdx: Idx,
    LocalIdx: Idx,
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

    // TODO(proof): `variant_fields.len() - 1` needs `variant_fields` non-empty
    // (README 段階 7, "残る前提: variant_fields が空でない"); out of scope for
    // overflow itself (debug-assertions off) but feeds `tag`'s `valid_range`.
    let max_discr = (variant_fields.len() - 1) as u128;
    let discr_int = Integer::fit_unsigned(max_discr);
    let tag = Scalar::Initialized {
        value: Primitive::Int(discr_int, false),
        valid_range: WrappingRange {
            start: 0,
            end: max_discr,
        },
    };

    let promoted_layouts = ineligible_locals.iter().map(|local| local_layouts[local]);
    prefix_layouts.push(tag_to_layout(tag));
    prefix_layouts.extend(promoted_layouts);
    // TODO(proof): `prefix_layouts.len() == 元の長さ + 1 + card(ineligible_locals)`
    // (README 段階 7) is needed for `b_start <= offsets.len()` below.
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
            // <= offsets.raw.len()`, i.e. `tag_index + 1 <= len` -- from
            // univariant's stage-6 contract (`offsets.len() == fields.len()`)
            // together with the prefix-length fact above (not wired up: see
            // the report on univariant.rs's own `ensures(true)`).
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
                // TODO(proof): `invert_bijective_mapping`'s (dropped)
                // debug_assert needs `in_memory_order_b` to enumerate
                // `0..in_memory_order_b.len()` exactly once -- the
                // permutation-split fact `lemma_permutation_split` below is
                // meant to supply this; not called here per the task.
                in_memory_order_b.invert_bijective_mapping(),
            )
        }
        _ => unreachable!(), // TODO(proof): unreachable because `univariant` always returns `FieldsShape::Arbitrary` (its own stage-6 `ensures`, not yet wired up here either).
    };

    let mut size = prefix.size;
    let mut align = prefix.align;
    let variants = variant_fields
        .iter_enumerated()
        .map(|(index, variant_fields)| {
            let variant_only_tys = variant_fields
                .iter()
                .filter(|local| match assignments[**local] {
                    // TODO(proof): unreachable by eligibility.rs's stage-5
                    // property 1 (an `Unassigned` local never appears in any
                    // variant's field list).
                    Unassigned => unreachable!(),
                    Assigned(v) if v == index => true,
                    // TODO(proof): unreachable by property 2 (`Assigned(v)`
                    // appears only under variant `v`).
                    Assigned(_) => unreachable!(),
                    Ineligible(_) => false,
                })
                .map(|local| local_layouts[*local]);

            let mut variant = match calc.univariant(
                &variant_only_tys.collect::<IndexVec<_, _>>(),
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
            let combined_offsets = variant_fields
                .iter_enumerated()
                .map(|(i, local)| {
                    let (offset, memory_index) = match assignments[*local] {
                        Unassigned => unreachable!(), // TODO(proof): as above.
                        Assigned(_) => {
                            // TODO(proof): `.unwrap()` needs
                            // `offsets_and_memory_index` to have as many
                            // entries left as there are `Assigned` locals
                            // still to visit -- README 段階 7, "Assigned の
                            // 個数が variant_only_tys の長さ...と一致する".
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
                                // -- README 段階 7.
                                promoted_offsets[field_idx],
                                promoted_memory_index[field_idx],
                            )
                        }
                    };
                    // TODO(proof): `combined_in_memory_order[memory_index]`
                    // needs `promoted_memory_index.len() + memory_index <
                    // invalid_field_idx` -- README 段階 7 (memory_index is a
                    // permutation's inverse, so `< len`; promoted_memory_index
                    // entries are likewise `< len`).
                    combined_in_memory_order[memory_index] = i;
                    offset
                })
                .collect();

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
            // `Arbitrary` above (README 段階 7, "到達しない").
            Ok(VariantLayout::from_layout(variant))
        })
        .collect::<Result<IndexVec<VariantIdx, _>, _>>()?;

    size = size.align_to(align.abi);

    let uninhabited = prefix.uninhabited || variants.iter().all(|v| v.is_uninhabited());
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

// //== stage 7 trusted lemma skeleton (README.md, 段階 7): "a/b 分割" fact.
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
#[thrust::trusted]
#[thrust_macros::requires(
    order.raw.len() == n
        && forall(|k: usize| !(0 <= k && k < n) || order.raw[k].index() < n)
        && forall(|k: usize, k2: usize| !(0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2))
            || !(order.raw[k].index() == order.raw[k2].index()))
        && b_start <= n
)]
#[thrust_macros::ensures(
    result.raw.len() == n - b_start
        && forall(|k: usize| !(0 <= k && k < result.raw.len()) || result.raw[k].index() < n - b_start)
        && forall(|k: usize, k2: usize|
            !(0 <= k && k < result.raw.len() && 0 <= k2 && k2 < result.raw.len() && !(k == k2))
            || !(result.raw[k].index() == result.raw[k2].index()))
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
            panic!("Use of unknown address space {c:?}");
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
            panic!("Use of unknown address space {c:?}");
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

    #[thrust::trusted]
    #[thrust::callable]
    pub fn from_bits(bits: impl TryInto<u64>) -> Size {
        let bits = bits.try_into().ok().unwrap();
        Size {
            raw: bits.div_ceil(8),
        }
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn from_bytes(bytes: impl TryInto<u64>) -> Size {
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
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

#[derive(Copy, Clone /*Debug*/)]
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
    // See univariant.rs for the intended contract and the three obstacles
    // that keep it at `ensures(true)` here too.
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    pub fn univariant<
        'a,
        FieldIdx: Idx,
        VariantIdx: Idx,
        F: Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy,
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

// //== Thrust model declarations

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
impl<'a, T> thrust_models::Model for SliceIter<'a, T> {
    type Ty = Self;
}
impl<'a, I: Idx, T> thrust_models::Model for IterEnumerated<'a, I, T> {
    type Ty = Self;
}
impl<I: Idx, T> thrust_models::Model for IndexVec<I, T> {
    type Ty = Self;
}
// See eligibility.rs/univariant.rs for why `type Ty = Self` is impossible for
// `IndexSlice` (unsized `raw: [T]`) and why the `[T]` model is reused.
impl<I: Idx, T: thrust_models::Model> thrust_models::Model for IndexSlice<I, T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}
impl<VariantIdx, FieldIdx> thrust_models::Model for SavedLocalEligibility<VariantIdx, FieldIdx> {
    type Ty = Self;
}
impl<F> thrust_models::Model for LayoutCalculatorError<F> {
    type Ty = Self;
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
