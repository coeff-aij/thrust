// `thrust_place_field_fail`, `thrust_place_fields_fail` and `thrust_permutation_sum_fail` are set
// only by the fail twins of the place_field, place_fields and permutation_sum roots.
#![allow(unexpected_cfgs)]
use crate::thrust_models;
use std::cmp;
use std::ops::Deref;

use thrust_models::model::{BitVec, Int, Seq, UInt};
use thrust_models::{exists, forall, Ghost};

use crate::rustc_abi::{
    AbiAlign, Align, AddressSpace, BackendRepr, FieldsShape, HasDataLayout, LayoutData, Niche,
    PointerSpec, Primitive, ReprOptions, Scalar, Size, StructKind, TargetDataLayout, Variants,
};
use crate::rustc_hashes::Hash64;
use crate::rustc_index::{Idx, IndexSlice, IndexVec};
use crate::case_study::USize;
use crate::case_study::lemmas;
use crate::case_study::iter::{Filter, Map, collect_index_vec, iter_all};

mod coroutine;
mod simple;

enum NicheBias {
    Start,
    End,
}

impl thrust_models::Model for NicheBias {
    type Ty = Self;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Copy, Debug)]
pub struct LayoutCalculator<Cx> {
    pub cx: Cx,
}

/// `2^q`, the bytes of `Align { pow2: q }` below 64, where `Align::bytes` gives `1 << (q & 63)`;
/// above, `2^q` overcounts it, so a weight stays an upper bound. Unsigned and unbounded: every
/// value is `>= 0`, which a weight needs, and none is checked below `2^64`, also where
/// `THRUST_INT_RANGE` gives `USize` its width.
#[thrust_macros::logic]
#[thrust_macros::variant(q)]
pub(crate) fn pow2(q: u64) -> UInt {
    if q <= 0 { 1 } else { pow2(q - 1) * 2 }
}

/// `1 << q` on 64-bit words, which `Align::bytes` and `Size::align_to` state, is `2^q` below 64,
/// by induction over `q`.
#[thrust_macros::lemma]
#[thrust_macros::variant(q)]
#[thrust_macros::ensures(q < 64 ==> pow2(q)
    == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int())]
pub(crate) fn shl_is_pow2(q: u64) {
    if q > 0 {
        shl_is_pow2(q - 1);
    }
}

/// The sum of the first `k` entries of `ts`. A sum, it is an `Int` over `Int`s, as `ones` is: at
/// `u64` its result would be checked `>= 0` without the facts of the sequence's elements, which
/// the README says such a sum cannot be shown.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn sum_first(ts: Seq<Int>, k: USize) -> Int {
    if k <= 0 { 0 } else { sum_first(ts, k - 1) + ts[k - 1] }
}

/// The sum of the entries of `ts` at the indices the first `k` entries of `s` hold: the weight of
/// the fields placed first, with `ts` the fields' weights and `s` the memory order.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn sum_at<I: Idx + thrust_models::Model>(ts: Seq<Int>, s: IndexVec<u32, I>, k: USize) -> Int {
    if k <= 0 { 0 } else { sum_at::<I>(ts, s, k - 1) + ts[I::index_logic(s[k - 1])] }
}

/// The sum of the first `m` entries of `ts` whose index occurs among the first `k` entries of `s`.
#[thrust_macros::logic]
#[thrust_macros::variant(m)]
fn sum_occurring<I: Idx + thrust_models::Model>(ts: Seq<Int>, s: IndexVec<u32, I>, k: USize, m: USize) -> Int {
    if m <= 0 {
        0
    } else if lemmas::occ::<I>(m - 1, s, k) > 0 {
        sum_occurring::<I>(ts, s, k, m - 1) + ts[m - 1]
    } else {
        sum_occurring::<I>(ts, s, k, m - 1)
    }
}

/// Entry `k - 1` of `s`, whose index does not occur before it, adds the entry of `ts` at its index.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::requires(k > 0 && lemmas::occ::<I>(I::index_logic(s[k - 1]), s, k - 1) == 0)]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, x: USize| x == I::index_logic(s[k - 1]) && x < m
    ==> sum_occurring::<I>(ts, s, k, m) == sum_occurring::<I>(ts, s, k - 1, m) + ts[x]))]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, x: USize| x == I::index_logic(s[k - 1]) && x >= m
    ==> sum_occurring::<I>(ts, s, k, m) == sum_occurring::<I>(ts, s, k - 1, m)))]
fn sum_occurring_step<I: Idx + thrust_models::Model>(s: Ghost<IndexVec<u32, I>>, k: usize, m: usize) {
    if m > 0 {
        sum_occurring_step(s, k, m - 1);
    }
}

/// Up to the first `k` entries of `s`, distinct and below `n`, sum `ts` as the indices that occur.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(lemmas::distinct::<I>(s, k))]
#[thrust_macros::requires(forall(|j: USize| 0 <= j && j < k ==> I::index_logic(s[j]) < n))]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, j: USize| 0 <= j && j <= k
    ==> sum_at::<I>(ts, s, j) == sum_occurring::<I>(ts, s, j, n)))]
fn sum_at_occurring<I: Idx + thrust_models::Model>(s: Ghost<IndexVec<u32, I>>, k: usize, n: usize) {
    if k > 0 {
        sum_at_occurring(s, k - 1, n);
        lemmas::absent(s, k - 1, k - 1);
        sum_occurring_step(s, k, n);
    }
}

/// The first `m` entries of `ts` whose index occurs sum to at most all of them, none being
/// negative.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, k: USize| forall(|i: USize| 0 <= i && i < m ==> ts[i] >= 0)
    ==> sum_occurring::<I>(ts, s, k, m) <= sum_first(ts, m)))]
fn sum_occurring_le<I: Idx + thrust_models::Model>(s: Ghost<IndexVec<u32, I>>, m: usize) {
    if m > 0 {
        sum_occurring_le(s, m - 1);
    }
}

/// The permutation sum: the entries of `ts` at the indices the first `k <= n` entries of `s` hold,
/// which are distinct and below `n`, sum to at most the first `n`, none of which is negative. The
/// fields placed first in memory order weigh at most all the fields.
#[thrust_macros::lemma]
#[thrust_macros::requires(lemmas::distinct::<I>(s, n))]
#[thrust_macros::requires(forall(|j: USize| 0 <= j && j < n ==> I::index_logic(s[j]) < n))]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, k: USize|
    0 <= k && k <= n && forall(|i: USize| 0 <= i && i < n ==> ts[i] >= 0)
        ==> sum_at::<I>(ts, s, k) <= sum_first(ts, n)))]
fn sum_at_le<I: Idx + thrust_models::Model>(s: Ghost<IndexVec<u32, I>>, n: usize) {
    sum_at_occurring(s, n, n);
    sum_occurring_le(s, n);
}

// The fail twin of the permutation_sum root sets this cfg: `sum_at_le` with its proof unchanged
// and without the distinct indices it needs, under which an index counted twice can exceed the sum.
#[cfg(thrust_permutation_sum_fail)]
#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|j: USize| 0 <= j && j < n ==> I::index_logic(s[j]) < n))]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, k: USize|
    0 <= k && k <= n && forall(|i: USize| 0 <= i && i < n ==> ts[i] >= 0)
        ==> sum_at::<I>(ts, s, k) <= sum_first(ts, n)))]
fn sum_at_le_repeated<I: Idx + thrust_models::Model>(s: Ghost<IndexVec<u32, I>>, n: usize) {
    sum_at_occurring(s, n, n);
    sum_occurring_le(s, n);
}

/// `pow2` is monotone.
#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::requires(a <= b)]
#[thrust_macros::ensures(pow2(a) <= pow2(b))]
fn pow2_mono(a: u64, b: u64) {
    if a < b {
        pow2_mono(a, b - 1);
    }
}

/// The bytes of any alignment, `1 << (q & 63)`, are at most `2^q` and at most `2^63`.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|b: USize| b == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int()
    ==> (b <= pow2(q) && b <= 9223372036854775808u64)))]
fn bytes_within(q: u64) {
    shl_is_pow2(q & 63);
    pow2_mono(q & 63, q);
}

/// `Size::align_to`'s result `r` in `pow2` terms, for any alignment and an offset up to `2^62`.
#[thrust_macros::lemma]
#[thrust_macros::requires(x.raw <= 4611686018427387904u64)]
#[thrust_macros::requires(forall(|b: USize|
    b == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(a.pow2) & BitVec::from_int(63))).to_int()
    && x.raw + b - 1 <= u64::MAX
    ==> (x.raw <= r.raw && r.raw < x.raw + b)))]
#[thrust_macros::ensures(forall(|q: USize| q == a.pow2
    ==> (x.raw <= r.raw && r.raw < x.raw + pow2(q) && r.raw < x.raw + 9223372036854775808u64)))]
fn aligned_within(x: Size, a: Align, r: Size) {
    bytes_within(a.pow2 as u64);
}

/// `pow2` is positive.
#[thrust_macros::lemma]
#[thrust_macros::variant(q)]
#[thrust_macros::ensures(pow2(q) >= 1)]
fn pow2_pos(q: u64) {
    if q > 0 {
        pow2_pos(q - 1);
    }
}

/// `niche`, if any, is well formed under `dl` and ends at or before `end`.
#[thrust_macros::predicate]
#[thrust::opaque]
fn niche_ends_by(niche: Option<Niche>, dl: TargetDataLayout, end: Size) -> bool {
    forall(|n: Niche, s: Size| !(niche == Some(n))
        || (Niche::wf_in(n, dl) && (!Primitive::size_in(n.value, dl, s) || n.offset.raw + s.raw <= end.raw)))
}

/// No niche ends by any end.
#[thrust_macros::lemma]
#[thrust_macros::ensures(niche_ends_by(None, *dl, end))]
#[thrust::reveal(niche_ends_by)]
fn no_niche_ends_by(dl: &TargetDataLayout, end: Size) {}

/// A niche that ends by `end` ends by any later end.
#[thrust_macros::lemma]
#[thrust_macros::requires(end.raw <= later.raw && niche_ends_by(*niche, *dl, end))]
#[thrust_macros::ensures(niche_ends_by(*niche, *dl, later))]
#[thrust::reveal(niche_ends_by)]
fn niche_ends_later(niche: &Option<Niche>, dl: &TargetDataLayout, end: Size, later: Size) {}

/// A niche well formed under `dl` has a primitive with a size there; `k` is the number of entries
/// of `address_space_info`.
#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|nn: Niche| niche == Some(nn) ==> Niche::wf_in(nn, *dl)))]
#[thrust_macros::requires(forall(|s: Seq<(AddressSpace, PointerSpec)>| s == (*dl).address_space_info ==> s.len() == k))]
#[thrust_macros::ensures(forall(|nn: Niche| niche == Some(nn) ==> exists(|s: Size| Primitive::size_in(nn.value, *dl, s))))]
fn niche_sized(niche: Option<Niche>, dl: &TargetDataLayout, k: usize) {
    if let Some(nn) = niche {
        super::size_in_total(nn.value, dl, k);
    }
}

// Stage 6 spec (README.md, "stage 6"). The `requires` of both methods is the panic condition of
// `univariant_biased` apart from the size: `fields.indices()` builds every field index up to
// `fields.len()`, the single variant is `VariantIdx::new(0)`, and `MaybeUnsized` takes
// `fields.len() - 1`, which wraps below zero (overflow checks are off) so that the slice `[..end]`
// panics; `dl_wf` of the data layout `self.cx` names (the default pointer size is 2, 4 or 8
// bytes, which `Size::checked_add` needs), named by `Cx::dl_of(*self, dl)` since the calculator's
// model is `self.cx`'s; `niche_wf` of every field's largest niche under that layout
// (`Niche::wf_in`, which `Niche::available` and `Primitive::size` need), the field's layout named
// by `post!` of `Deref::deref` (probes/layout_ref_niche.rs); every field's niche within the
// field, which rustc's layouts satisfy and the sort key's subtractions and the niche of the
// result rely on; and `Scalar::wf_in` of every field whose `backend_repr` is a scalar, which
// `scalar_pair` requires of the two scalars it pairs. Like `niche_wf`, the last is an invariant of
// the layouts rustc computes, not a check of the caller's. The one panic of the offset arithmetic
// is `niche.offset += offset` (`Size::add` on an overflow); `align_to` and `Align::bytes` wrap
// without overflow checks and `checked_add` returns `None`. It needs the prefix's and each field's
// size below the object size bound: then the offset a field is placed at is below the bound plus
// the field's alignment mask (`2^63 - 1` at most, so no rounding wraps), and the niche's offset is
// within its field (`Primitive::size_in` gives every primitive a size, `size_in_total`), so the sum
// stays below `2^64`. A field's size is that of a layout rustc computed, and so is the prefix's
// (the tag's, or the prefix layout's in `layout()`); every layout constructor checks it against
// the bound. No alignment needs a bound, but the first field is placed after the prefix rounded
// to its alignment, which both methods require to end by `2^62` (`prefix_fits`): the offset a
// field is placed at then stays below `2^62 + 2^63`, as the alignment's bytes are at most `2^63`.
//
// `univariant_biased` ensures, besides `arbitrary_of`: it fails only with `UnexpectedUnsized` or
// `SizeOverflow`; `UnexpectedUnsized` only when an unsized field is not the tail of a
// `MaybeUnsized` struct, which does not depend on the order, and then with one of the two, as
// the loop returns `SizeOverflow` at a field before the unsized one when the offset overflows
// there; `SizeOverflow` never when the fields fit in any order (`fits_in_any_order`), so that
// under it a misplaced unsized field gives `UnexpectedUnsized`; with `Start` a niche comes from
// some field's, and with `End` any field's niche gives one; the niche is well formed and lies
// within the size. Both methods also require
// that `F`'s `deref` is a function (`deref_functional`): the code reads each field's layout once,
// so the directions that conclude from some layout `post!` allows (an unsized field gives
// `UnexpectedUnsized`, a field's niche gives `End` one) hold only for the layout `deref` returns. `univariant` needs these
// for its two `expect`s on the `End` layout, and requires that the fields fit in any
// order: rustc assumes the `End` layout succeeds whenever the `Start` one does
// (`expect("alt layout should always work")`), but the two orders pad differently, so one of them
// can overflow `checked_add` or `obj_size_bound` alone; summing every field's size and twice its
// alignment, with the prefix, the aggregate and `repr` alignments, bounds the size of every order.
// rustc's callers do not guarantee this bound: they pass any fields and handle `SizeOverflow`. It
// is a scope restriction, to fields whose sum is below the object size bound, under which no
// `SizeOverflow` path is taken. What the `expect` needs is only that `End` succeeds when `Start`
// does, which no contract states without a model of the padding of the two orders.
//
// Both methods also ensure that an `Ok` layout's size is below that sum S (`weighs`) and its
// alignment at most S, which `layout()` needs to bound the prefix its variants start with. The
// first field starts below ps + 2^pa (the prefix's size and alignment), each field adds at most
// 2^a - 1 of padding and its size s, and the final padding is below the alignment, which is one of
// the field's 2^a, the prefix's 2^pa, the `repr` alignment or the aggregate or `i8` alignment
// (`pack` only lowers them): each is a summand of S not yet spent, as S counts a field's and the
// prefix's alignment twice. `univariant` proves it from its two calls; `univariant_biased` is
// verified against it in its own root, and the other roots take it as part of its contract.
// They ensure too that an `Ok` layout is one `layout_pre` accepts as a field or a prefix, which
// `layout()` passes the prefix's layout on as: its size below the object size bound, for which
// the final check `size.bytes() >= dl.obj_size_bound()` returns `SizeOverflow`.
#[thrust_macros::context]
impl<Cx: HasDataLayout> LayoutCalculator<Cx> {
    /// The panic condition of `univariant` and `univariant_biased` apart from the size.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn layout_pre<
        'a,
        FieldIdx: Idx + thrust_models::Model,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    >(
        self,
        fields: &IndexSlice<FieldIdx, F>,
        kind: StructKind,
    ) -> bool {
        forall(|k: USize| !(0 <= k && k <= (*fields).len()) || <FieldIdx as Idx>::can_new(k))
            && forall(|z: USize| !(z == 0usize) || <VariantIdx as Idx>::can_new(z))
            && (!matches!(kind, StructKind::MaybeUnsized) || (*fields).len() > 0)
            && forall(|dl: TargetDataLayout| !Cx::dl_of(self, dl)
                || dl.default_address_space_pointer_spec.pointer_size.raw == 2
                || dl.default_address_space_pointer_spec.pointer_size.raw == 4
                || dl.default_address_space_pointer_spec.pointer_size.raw == 8)
            && forall(|dl: TargetDataLayout, ps: Size, pa: Align|
                !(Cx::dl_of(self, dl) && kind == StructKind::Prefixed(ps, pa))
                    || ps.raw < super::obj_bound(dl))
            && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>|
                !(Cx::dl_of(self, dl)
                    && 0 <= i
                    && i < (*fields).len()
                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l)
                    || l.size.raw < super::obj_bound(dl))
            && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
                !(Cx::dl_of(self, dl)
                    && 0 <= i
                    && i < (*fields).len()
                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l
                    && l.largest_niche == Some(n))
                    || Niche::wf_in(n, dl))
            && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, s: Size|
                !(Cx::dl_of(self, dl)
                    && 0 <= i
                    && i < (*fields).len()
                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l
                    && l.largest_niche == Some(n)
                    && Primitive::size_in(n.value, dl, s))
                    || n.offset.raw + s.raw <= l.size.raw)
            && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, c: Scalar|
                !(Cx::dl_of(self, dl)
                    && 0 <= i
                    && i < (*fields).len()
                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l
                    && l.backend_repr == BackendRepr::Scalar(c))
                    || Scalar::wf_in(c, dl))
    }

    /// The no-overflow condition of placing the first field after a prefix: the prefix's size plus
    /// the bytes `b` of its alignment after `pack` is at most `2^62`.
    #[thrust_macros::predicate]
    pub(crate) fn prefix_fits(repr: &ReprOptions, kind: StructKind) -> bool {
        forall(|ps: Size, pa: Align, q: USize, b: USize|
            !(kind == StructKind::Prefixed(ps, pa)
                && (q == pa.pow2 || exists(|p: Align| (*repr).pack == Some(p) && p.pow2 < pa.pow2 && q == p.pow2))
                && b == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int())
                || ps.raw + b <= 4611686018427387904u64)
    }

    /// `w` is the weight of `fields`: the sum of each field's size and twice its alignment.
    #[thrust_macros::predicate]
    pub(crate) fn weight<
        'a,
        I: Idx,
        FieldIdx: Idx + thrust_models::Model,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    >(
        fields: &IndexSlice<I, F>,
        w: USize,
    ) -> bool {
        exists(|ts: Seq<Int>|
            ts.len() == (*fields).len()
                && forall(|i: USize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, q: USize|
                    !(0 <= i && i < ts.len() && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l && q == l.align.abi.pow2)
                        || ts[i] == pow2(q) * 2 + l.size.raw)
                && w == sum_first(ts, ts.len()))
    }

    /// `s` is the weight of `fields` with the prefix's size and twice its alignment, the `repr`
    /// alignment and the aggregate and `i8` alignments of `dl`. It bounds the size and the
    /// alignment of every order of the fields.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn weighs<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        fields: &IndexSlice<FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
        dl: TargetDataLayout,
        s: USize,
    ) -> bool {
        exists(|w: USize, p: USize, r: USize, qa: USize, qi: USize|
            Self::weight::<FieldIdx, FieldIdx, VariantIdx, F>(fields, w)
                && ((forall(|ps: Size, pa: Align| kind != StructKind::Prefixed(ps, pa)) && p == 0)
                    || exists(|ps: Size, pa: Align, q: USize|
                        kind == StructKind::Prefixed(ps, pa) && q == pa.pow2 && p == pow2(q) * 2 + ps.raw))
                && (((*repr).align == None && r == 0)
                    || exists(|ra: Align, q: USize| (*repr).align == Some(ra) && q == ra.pow2 && r == pow2(q)))
                && qa == dl.aggregate_align.pow2
                && qi == dl.i8_align.pow2
                && s == w + p + r + pow2(qa) + pow2(qi))
    }

    /// Every order of the fields stays below the object size bound of the data layout.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub(crate) fn fits_in_any_order<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        self,
        fields: &IndexSlice<FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
    ) -> bool {
        forall(|dl: TargetDataLayout| !Cx::dl_of(self, dl)
            || exists(|s: USize, b: USize|
                Self::weighs::<FieldIdx, VariantIdx, F>(fields, repr, kind, dl, s)
                    && ((dl.default_address_space_pointer_spec.pointer_size.raw == 2 && b == 32768u64)
                        || (dl.default_address_space_pointer_spec.pointer_size.raw == 4 && b == 2147483648u64)
                        || (dl.default_address_space_pointer_spec.pointer_size.raw == 8 && b == 2305843009213693952u64))
                    && s < b))
    }

    /// `F`'s `deref` is a function: each value of `F` dereferences to one layout. `post!` of a
    /// generic `Deref::deref` is a relation, as Creusot's `T::deref.postcondition` is, so a
    /// contract that names a field's layout by `exists d. post!(.., d) && **d == l` speaks of every
    /// layout the relation allows; this predicate makes that the one layout `deref` returns.
    /// rustc's `Layout` dereferences to the interned pointer it holds.
    #[thrust_macros::predicate]
    pub(crate) fn deref_functional<
        'a,
        FieldIdx: Idx + thrust_models::Model,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    >() -> bool {
        forall(|x: <F as thrust_models::Model>::Ty, d1: &&LayoutData<FieldIdx, VariantIdx>, d2: &&LayoutData<FieldIdx, VariantIdx>|
            !(thrust_macros::post!(<F as core::ops::Deref>::deref(&x), d1)
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&x), d2))
                || **d1 == **d2)
    }

    /// An invariant of the layouts rustc computes that `place_field` relies on: the size below the
    /// object size bound, and the niche well formed, starting within the field and ending by its
    /// end where its primitive has a size.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    fn field_wf<FieldIdx: Idx + thrust_models::Model, VariantIdx: Idx>(
        l: LayoutData<FieldIdx, VariantIdx>,
        dl: TargetDataLayout,
    ) -> bool {
        l.size.raw < super::obj_bound(dl)
            && forall(|n: Niche, s: Size| !(l.largest_niche == Some(n))
                || (Niche::wf_in(n, dl)
                    && n.offset.raw <= l.size.raw
                    && (!Primitive::size_in(n.value, dl, s) || n.offset.raw + s.raw <= l.size.raw)))
    }

    /// What `place_fields` needs of every field's layout, which `layout_pre` states: the size below
    /// the object size bound, and the niche well formed and ending by the field's end where its
    /// primitive has a size.
    #[thrust_macros::predicate]
    fn fields_ok<
        'a,
        FieldIdx: Idx + thrust_models::Model,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    >(
        fields: &IndexSlice<FieldIdx, F>,
        dl: TargetDataLayout,
    ) -> bool {
        forall(|i: USize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, s: Size|
            !(0 <= i && i < (*fields).len() && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l)
                || (l.size.raw < super::obj_bound(dl)
                    && (!(l.largest_niche == Some(n))
                        || (Niche::wf_in(n, dl) && (!Primitive::size_in(n.value, dl, s) || n.offset.raw + s.raw <= l.size.raw)))))
    }

    /// `ts` holds each field's weight: its size and twice its alignment's bytes.
    #[thrust_macros::predicate]
    fn weights_are<
        'a,
        FieldIdx: Idx + thrust_models::Model,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    >(
        fields: &IndexSlice<FieldIdx, F>,
        ts: Seq<Int>,
    ) -> bool {
        ts.len() == (*fields).len()
            && forall(|i: USize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, q: USize|
                !(0 <= i && i < ts.len() && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l && q == l.align.abi.pow2)
                    || ts[i] == pow2(q) * 2 + l.size.raw)
    }

    /// `order` is a permutation of the `n` field indices, which holds the last field last when
    /// the struct is `MaybeUnsized`.
    #[thrust_macros::predicate]
    fn order_ok<FieldIdx: Idx + thrust_models::Model>(order: IndexVec<u32, FieldIdx>, n: USize, kind: StructKind) -> bool {
        order.len() == n
            && lemmas::distinct::<FieldIdx>(order, n)
            && forall(|j: USize| !(0 <= j && j < n) || <FieldIdx as Idx>::index_logic(order[j]) < n)
            && forall(|i: USize| !(0 <= i && i < n)
                || exists(|j: USize| 0 <= j && j < n && <FieldIdx as Idx>::index_logic(order[j]) == i))
            && (!matches!(kind, StructKind::MaybeUnsized) || <FieldIdx as Idx>::index_logic(order[n - 1]) == n - 1)
    }

    /// An unsized field is not the tail of a `MaybeUnsized` struct.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    fn unsized_misplaced<
        'a,
        FieldIdx: Idx + thrust_models::Model,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    >(
        fields: &IndexSlice<FieldIdx, F>,
        kind: StructKind,
    ) -> bool {
        exists(|i: USize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>|
            0 <= i && i < (*fields).len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l
                && l.backend_repr == BackendRepr::Memory { sized: false }
                && (!matches!(kind, StructKind::MaybeUnsized) || i + 1 < (*fields).len()))
    }

    /// Some field has a largest niche.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    fn some_field_niche<
        'a,
        FieldIdx: Idx + thrust_models::Model,
        VariantIdx: Idx,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    >(
        fields: &IndexSlice<FieldIdx, F>,
    ) -> bool {
        exists(|i: USize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
            0 <= i && i < (*fields).len() && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l && l.largest_niche == Some(n))
    }

    #[thrust_macros::requires(Self::layout_pre::<FieldIdx, VariantIdx, F>(*self, fields, kind))]
    #[thrust_macros::requires(Self::prefix_fits(repr, kind))]
    #[thrust_macros::requires(Self::deref_functional::<FieldIdx, VariantIdx, F>())]
    #[thrust_macros::requires(Self::fits_in_any_order::<FieldIdx, VariantIdx, F>(*self, fields, repr, kind))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>|
        result != Ok(l) || FieldsShape::<FieldIdx>::arbitrary_of(l.fields, (*fields).len())))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>, dl: TargetDataLayout, s: USize, q: USize|
        result == Ok(l)
            && Cx::dl_of(*self, dl)
            && Self::weighs::<FieldIdx, VariantIdx, F>(fields, repr, kind, dl, s)
            && q == l.align.abi.pow2 ==> (l.size.raw < s && pow2(q) <= s)))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>, dl: TargetDataLayout|
        result == Ok(l) && Cx::dl_of(*self, dl) ==> l.size.raw < super::obj_bound(dl)))]
    #[thrust::reveal(LayoutCalculator::layout_pre)]
    pub fn univariant<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        &self,
        fields: &IndexSlice<FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
    ) -> LayoutCalculatorResult<FieldIdx, VariantIdx, F>
    where
        Cx: thrust_models::Model<Ty: PartialEq>,
    {
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
                            .expect("alt layout should always work");
                        let alt_niche = alt_layout
                            .largest_niche
                            .expect("alt layout should have a niche like the regular one");
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

    #[thrust_macros::requires(Self::layout_pre::<FieldIdx, VariantIdx, F>(*self, fields, kind))]
    #[thrust_macros::requires(Self::prefix_fits(repr, kind))]
    #[thrust_macros::requires(Self::deref_functional::<FieldIdx, VariantIdx, F>())]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>|
        result != Ok(l) || FieldsShape::<FieldIdx>::arbitrary_of(l.fields, (*fields).len())))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>, dl: TargetDataLayout, s: USize, q: USize|
        result == Ok(l)
            && Cx::dl_of(*self, dl)
            && Self::weighs::<FieldIdx, VariantIdx, F>(fields, repr, kind, dl, s)
            && q == l.align.abi.pow2 ==> (l.size.raw < s && pow2(q) <= s)))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>, dl: TargetDataLayout|
        result == Ok(l) && Cx::dl_of(*self, dl) ==> l.size.raw < super::obj_bound(dl)))]
    #[thrust_macros::ensures(forall(|e: LayoutCalculatorError<<F as thrust_models::Model>::Ty>|
        result != Err(e)
            || e == LayoutCalculatorError::SizeOverflow
            || exists(|f: <F as thrust_models::Model>::Ty| e == LayoutCalculatorError::UnexpectedUnsized(f))))]
    #[thrust_macros::ensures(
        (exists(|f: <F as thrust_models::Model>::Ty| result == Err(LayoutCalculatorError::UnexpectedUnsized(f)))
            ==> Self::unsized_misplaced::<FieldIdx, VariantIdx, F>(fields, kind))
        && (Self::unsized_misplaced::<FieldIdx, VariantIdx, F>(fields, kind)
            ==> (exists(|f: <F as thrust_models::Model>::Ty| result == Err(LayoutCalculatorError::UnexpectedUnsized(f)))
                || result == Err(LayoutCalculatorError::SizeOverflow))))]
    #[thrust_macros::ensures(
        Self::fits_in_any_order::<FieldIdx, VariantIdx, F>(*self, fields, repr, kind) ==> result != Err(LayoutCalculatorError::SizeOverflow))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>| result != Ok(l)
        || ((matches!(niche_bias, NicheBias::Start) && l.largest_niche != None) ==> Self::some_field_niche::<FieldIdx, VariantIdx, F>(fields))
            && ((matches!(niche_bias, NicheBias::End) && Self::some_field_niche::<FieldIdx, VariantIdx, F>(fields)) ==> l.largest_niche != None)))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>, n: Niche, dl: TargetDataLayout, s: Size|
        result == Ok(l) && l.largest_niche == Some(n) && Cx::dl_of(*self, dl) ==> (Niche::wf_in(n, dl) && (Primitive::size_in(n.value, dl, s) ==> n.offset.raw + s.raw <= l.size.raw))))]
    #[thrust::reveal(
        LayoutCalculator::layout_pre,
        LayoutCalculator::fits_in_any_order,
        LayoutCalculator::weighs,
        LayoutCalculator::unsized_misplaced,
        LayoutCalculator::some_field_niche,
        super::Primitive::size_in,
        super::FieldsShape::arbitrary_of
    )]
    fn univariant_biased<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        &self,
        fields: &IndexSlice<FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
        niche_bias: NicheBias,
    ) -> LayoutCalculatorResult<FieldIdx, VariantIdx, F>
    where
        Cx: thrust_models::Model<Ty: PartialEq>,
    {
        let dl = self.cx.data_layout();
        let pack = repr.pack;
        let mut align = if pack.is_some() {
            dl.i8_align
        } else {
            dl.aggregate_align
        };
        let mut max_repr_align = repr.align;
        // Rewrite (rewrites.md R8): `collect_index_vec` for `collect`.
        let mut in_memory_order: IndexVec<u32, FieldIdx> = collect_index_vec(fields.indices());
        thrust_macros::proof_assert!(|in_memory_order: IndexVec<u32, FieldIdx>, fields: &IndexSlice<FieldIdx, F>|
            in_memory_order.len() == (*fields).len()
                && forall(|j: USize| !(0 <= j && j < (*fields).len()) || <FieldIdx as Idx>::index_logic(in_memory_order[j]) == j));
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
                // Rewrite (rewrites.md R8): `Map::new(it, f)` for `it.map(f)`.
                let max_field_align = Map::new(fields_excluding_tail.iter(), thrust_macros::closure!(
                    requires(true),
                    ensures(true),
                    |f: &F| -> u64 { f.align.bytes() },
                ))
                .max()
                .unwrap_or(1);
                // Rewrite (rewrites.md R8): `Map::new` of the niche's `available`, 0 without one,
                // for `filter_map` of the niche and `map` of `available`: the two maxima agree,
                // as `available` is never negative.
                // Fallback (open parts 14 and 15): `Map::new` and `max` with their preconditions
                // assumed; restore `Map::new(..).max()` once the solver answers them.
                let largest_niche_size = crate::case_study::iter::max_assumed(crate::case_study::iter::map_new_assumed(fields_excluding_tail.iter(), thrust_macros::closure!(
                    captures(dl: &mut &&TargetDataLayout),
                    requires(forall(|d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
                        !(thrust_macros::post!(<F as core::ops::Deref>::deref(f), d) && (**d).largest_niche == Some(n))
                            || Niche::wf_in(n, ***dl))),
                    ensures(true),
                    |f: &F| -> u128 {
                        f.largest_niche.map_or(0, thrust_macros::closure!(
                            captures(dl: &&&TargetDataLayout),
                            requires(Niche::wf_in(n, ***dl)),
                            ensures(true),
                            |n: Niche| -> u128 { n.available(dl) },
                        ))
                    },
                ))
                )
                .unwrap_or(0);
                #[cfg(thrust_ub_reach = "largest_niche")]
                thrust_macros::proof_assert!(|kind: StructKind| false);

                // Rewrite (rewrites.md R20): the data layout as a parameter instead of a capture.
                let alignment_group_key = thrust_macros::closure!(
                    requires(forall(|d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
                        !(thrust_macros::post!(<F as core::ops::Deref>::deref(layout), d) && (**d).largest_niche == Some(n))
                            || Niche::wf_in(n, *dl))),
                    |layout: &F, dl: &TargetDataLayout| {
                        if let Some(pack) = pack {
                            layout.align.abi.min(pack).bytes()
                        } else {
                            let align = layout.align.bytes();
                            let size = layout.size.bytes();
                            // Fallback (open `map` goal): `map` with its precondition assumed;
                            // restore `layout.largest_niche.map(..)` once the solver answers it.
                            let niche_size = crate::case_study::iter::map_assumed(layout.largest_niche, thrust_macros::closure!(
                                captures(dl: &&TargetDataLayout),
                                requires(Niche::wf_in(n, **dl)),
                                ensures(true),
                                |n: Niche| -> u128 { n.available(dl) },
                            )).unwrap_or(0);
                            #[cfg(thrust_ub_reach = "map")]
                            thrust_macros::proof_assert!(|layout: &F| false);

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
                    },
                );

                match kind {
                    StructKind::AlwaysSized | StructKind::MaybeUnsized => {
                        // Fallback (open part 40): `sort_by_key` with its `requires` assumed, by
                        // `sort_by_key_assumed` of thrust/iter.rs, as the key closure's type
                        // cannot be written in an `assume!` here; restore `optimizing.sort_by_key`
                        // once the solver answers it.
                        crate::case_study::iter::sort_by_key_assumed(optimizing, thrust_macros::closure!(
                            captures(fields: &mut &IndexSlice<FieldIdx, F>, dl: &mut &&TargetDataLayout),
                            requires(LayoutCalculator::<Cx>::deref_functional::<FieldIdx, VariantIdx, F>()),
                            requires(forall(|i: USize| !<FieldIdx as Idx>::index_is(x, i) || i < (**fields).len())),
                            requires(forall(|i: USize, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
                                !(<FieldIdx as Idx>::index_is(x, i)
                                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(**fields)[i]), d)
                                    && (**d).largest_niche == Some(n))
                                    || Niche::wf_in(n, ***dl))),
                            requires(forall(|i: USize, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, s: Size|
                                !(<FieldIdx as Idx>::index_is(x, i)
                                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(**fields)[i]), d)
                                    && (**d).largest_niche == Some(n)
                                    && Primitive::size_in(n.value, ***dl, s))
                                    || n.offset.raw + s.raw <= (**d).size.raw)),
                            |&x: &FieldIdx| {
                                let f = &fields[x];
                                let field_size = f.size.bytes();
                                // Fallback (open `map_or` goals): the three `map_or` calls with their
                                // preconditions assumed; restore `f.largest_niche.map_or(..)` once
                                // the solver answers them.
                                let niche_size = crate::case_study::iter::map_or_assumed(f.largest_niche, 0, thrust_macros::closure!(
                                    captures(dl: &&&TargetDataLayout),
                                    requires(Niche::wf_in(n, ***dl)),
                                    ensures(true),
                                    |n: Niche| -> u128 { n.available(dl) },
                                ));
                                let niche_size_key = match niche_bias {
                                    NicheBias::Start => !niche_size,

                                    NicheBias::End => niche_size,
                                };
                                let inner_niche_offset_key = match niche_bias {
                                    NicheBias::Start => crate::case_study::iter::map_or_assumed(f.largest_niche, 0, thrust_macros::closure!(
                                        requires(true),
                                        ensures(true),
                                        |n: Niche| -> u64 { n.offset.bytes() },
                                    )),
                                    NicheBias::End => crate::case_study::iter::map_or_assumed(f.largest_niche, 0, thrust_macros::closure!(
                                        captures(field_size: &u64, dl: &&&TargetDataLayout),
                                        requires(Niche::wf_in(n, ***dl)),
                                        requires(forall(|s: Size| !Primitive::size_in(n.value, ***dl, s) || n.offset.raw + s.raw <= *field_size)),
                                        ensures(true),
                                        |n: Niche| -> u64 {
                                            // Fallback (open parts 98 and 99): the capture and the
                                            // niche's value size bound to locals so that an `assume!`
                                            // can state that the two subtractions do not underflow.
                                            // They hold in rustc: the niche lies within its field
                                            // (`requires` above, with `Primitive::size`'s
                                            // `ensures`); the solver does not answer them (killed
                                            // for memory). Restore the one expression once it does.
                                            let field_size: u64 = field_size;
                                            let value_size = n.value.size(dl).bytes();
                                            thrust_macros::assume!(|field_size: u64, value_size: u64| value_size <= field_size);
                                            thrust_macros::assume!(|n: Niche, field_size: u64, value_size: u64| n.offset.raw <= field_size - value_size);
                                            #[cfg(thrust_ub_reach = "niche_end_key")]
                                            thrust_macros::proof_assert!(|n: Niche| false);
                                            !(field_size - value_size - n.offset.bytes())
                                        },
                                    )),
                                };
                                #[cfg(thrust_ub_reach = "map_or")]
                                thrust_macros::proof_assert!(|x: FieldIdx| false);

                                // Fallback (open parts 39 and 95): the capture `dl` bound to a
                                // local by `as_local` (below), so that an `assume!` can state
                                // `alignment_group_key`'s `requires` at this call. It holds in
                                // rustc: `f` is the field at `x`, whose niche is well formed by
                                // this closure's `requires`; the solver does not answer it (killed
                                // for memory).
                                let key_dl: &TargetDataLayout = as_local(dl);
                                thrust_macros::assume!(|f: &F, key_dl: &TargetDataLayout|
                                    forall(|d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
                                        !(thrust_macros::post!(<F as core::ops::Deref>::deref(f), d) && (**d).largest_niche == Some(n))
                                            || Niche::wf_in(n, *key_dl)));
                                #[cfg(thrust_ub_reach = "alignment_group_key")]
                                thrust_macros::proof_assert!(|x: FieldIdx| false);
                                (
                                    cmp::Reverse(alignment_group_key(f, key_dl)),
                                    niche_size_key,
                                    inner_niche_offset_key,
                                )
                            },
                        ));
                        #[cfg(thrust_ub_reach = "sort")]
                        thrust_macros::proof_assert!(|kind: StructKind| false);
                    }

                    StructKind::Prefixed(..) => {
                        optimizing.sort_by_key(thrust_macros::closure!(
                            captures(fields: &mut &IndexSlice<FieldIdx, F>, dl: &mut &&TargetDataLayout),
                            requires(forall(|i: USize| !<FieldIdx as Idx>::index_is(x, i) || i < (**fields).len())),
                            requires(forall(|i: USize, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
                                !(<FieldIdx as Idx>::index_is(x, i)
                                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(**fields)[i]), d)
                                    && (**d).largest_niche == Some(n))
                                    || Niche::wf_in(n, ***dl))),
                            |&x: &FieldIdx| {
                                let f = &fields[x];
                                let niche_size = f.largest_niche.map_or(0, thrust_macros::closure!(
                                    captures(dl: &&&TargetDataLayout),
                                    requires(Niche::wf_in(n, ***dl)),
                                    ensures(true),
                                    |n: Niche| -> u128 { n.available(dl) },
                                ));
                                (alignment_group_key(f, dl), niche_size)
                            },
                        ));
                    }
                }
            }
        }

        // The memory order is a permutation of the fields that keeps a `MaybeUnsized` tail last:
        // the sort permutes the first `end` entries of the identity order and keeps the rest, so
        // the indices stay distinct and below `n`, and every field occurs by the pigeonhole
        // principle (`lemmas::every_index_occurs`).
        thrust_macros::proof_assert!(|in_memory_order: IndexVec<u32, FieldIdx>, fields: &IndexSlice<FieldIdx, F>, kind: StructKind|
            in_memory_order.len() == (*fields).len()
                && forall(|j: USize| !(0 <= j && j < (*fields).len()) || <FieldIdx as Idx>::index_logic(in_memory_order[j]) < (*fields).len())
                && (!matches!(kind, StructKind::MaybeUnsized)
                    || <FieldIdx as Idx>::index_logic(in_memory_order[(*fields).len() - 1]) == (*fields).len() - 1));
        thrust_macros::proof_assert!(|in_memory_order: IndexVec<u32, FieldIdx>, fields: &IndexSlice<FieldIdx, F>|
            lemmas::distinct::<FieldIdx>(in_memory_order, (*fields).len()));
        let order = thrust_macros::ghost!(|in_memory_order: IndexVec<u32, FieldIdx>| -> IndexVec<u32, FieldIdx> {
            in_memory_order
        });
        thrust_macros::proof!(lemmas::every_index_occurs(order, fields.len(), fields.len()));

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
        // Fallback: the two conjuncts of `place_fields`' `requires` the solver does not answer at
        // the call (`fields_ok`, from `layout_pre`; `order_ok`, from the facts asserted after the
        // sort), assumed exactly.
        thrust_macros::assume!(|fields: &IndexSlice<FieldIdx, F>, dl: &TargetDataLayout|
            LayoutCalculator::<Cx>::fields_ok::<FieldIdx, VariantIdx, F>(fields, *dl));
        thrust_macros::assume!(|in_memory_order: IndexVec<u32, FieldIdx>, fields: &IndexSlice<FieldIdx, F>, kind: StructKind|
            LayoutCalculator::<Cx>::order_ok::<FieldIdx>(in_memory_order, (*fields).len(), kind));
        #[cfg(thrust_ub_reach = "place_fields_pre")]
        thrust_macros::proof_assert!(|kind: StructKind| false);
        // Rewrite (rewrites.md R19): the field loop as `place_fields`.
        // Rewrite (rewrites.md, pending): `?` as a `match` that returns the error itself, so that
        // the error `place_fields`'s contract describes reaches the return without the
        // `Try::branch` and `FromResidual::from_residual` calls of `?`'s desugaring.
        let unsized_field = match Self::place_fields::<FieldIdx, VariantIdx, F>(
            fields,
            &in_memory_order,
            kind,
            pack,
            &niche_bias,
            dl,
            &mut offsets,
            &mut offset,
            &mut align,
            &mut max_repr_align,
            &mut largest_niche,
            &mut largest_niche_available,
        ) {
            Ok(unsized_field) => unsized_field,
            Err(e) => return Err(e),
        };

        let unadjusted_abi_align = align;
        if let Some(repr_align) = repr.align {
            align = align.max(repr_align);
        }

        let align = align;

        // debug!("univariant min_size: {:?}", offset);
        let min_size = offset;
        let size = min_size.align_to(align);

        // Assumed (fallback; open part 34, with fptprove): delete once the solver answers it.
        // `obj_size_bound`'s requires.
        thrust_macros::assume!(|dl: &TargetDataLayout| (*dl).default_address_space_pointer_spec.pointer_size.raw == 2
            || (*dl).default_address_space_pointer_spec.pointer_size.raw == 4
            || (*dl).default_address_space_pointer_spec.pointer_size.raw == 8);
        #[cfg(thrust_ub_reach = "obj_size_bound")]
        thrust_macros::proof_assert!(|kind: StructKind| false);
        if size.bytes() >= dl.obj_size_bound() {
            return Err(LayoutCalculatorError::SizeOverflow);
        }
        // Rewrite (rewrites.md, pending): the backend representation and the unadjusted alignment
        // by `backend_repr_of`, so that what the postcondition reads reaches the return without
        // the joins of that code.
        let sized = unsized_field.is_none();
        let (abi, unadjusted_abi_align) = self.backend_repr_of::<FieldIdx, VariantIdx, F>(
            fields, repr, kind, &offsets, align, size, sized, unadjusted_abi_align,
        );
        // Rewrite (rewrites.md R8): `!iter_all(it, |f| !p(f))` for `it.any(p)`.
        // Fallback (open part 57): `iter_all` with its precondition assumed; restore `iter_all` once
        // the solver answers it.
        let uninhabited = !crate::case_study::iter::iter_all_assumed(fields.iter(), |f| !f.is_uninhabited());
        #[cfg(thrust_ub_reach = "iter_all")]
        thrust_macros::proof_assert!(|kind: StructKind| false);


        let seed = field_seed.wrapping_add(repr.field_shuffle_seed);

        // Assumed (fallback; open part 58, with fptprove): delete once the solver answers it.
        // `VariantIdx::new(0)`'s requires.
        thrust_macros::assume!(|kind: StructKind| forall(|z: USize| z == 0usize ==> <VariantIdx as Idx>::can_new(z)));
        #[cfg(thrust_ub_reach = "variant_index")]
        thrust_macros::proof_assert!(|kind: StructKind| false);
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

    /// The backend representation of `univariant_biased`'s layout and its unadjusted alignment:
    /// the code `univariant_biased` runs after its size check, moved here (rewrite, rewrites.md
    /// pending) so that the values its postcondition reads reach its return without this
    /// code's joins. The body is checked; the contract says nothing of the result, which the
    /// postcondition does not read.
    #[thrust_macros::requires(Self::layout_pre::<FieldIdx, VariantIdx, F>(*self, fields, kind))]
    #[thrust_macros::requires(Self::deref_functional::<FieldIdx, VariantIdx, F>())]
    #[thrust_macros::ensures(true)]
    #[thrust::reveal(
        LayoutCalculator::layout_pre,
        LayoutCalculator::fits_in_any_order,
        LayoutCalculator::weighs,
        LayoutCalculator::unsized_misplaced,
        LayoutCalculator::some_field_niche,
        super::Primitive::size_in,
        super::FieldsShape::arbitrary_of
    )]
    fn backend_repr_of<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        &self,
        fields: &IndexSlice<FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
        offsets: &IndexVec<FieldIdx, Size>,
        align: Align,
        size: Size,
        sized: bool,
        unadjusted_abi_align: Align,
    ) -> (BackendRepr, Align)
    where
        Cx: thrust_models::Model<Ty: PartialEq>,
    {
        let mut layout_of_single_non_zst_field = None;
        let mut abi = BackendRepr::Memory { sized };

        let optimize_abi = !repr.inhibit_newtype_abi_optimization();

        if sized && size.bytes() > 0 {
            // Assumed (fallback; open part 35, with fptprove): delete once the solver answers it.
            // `iter_enumerated`'s requires.
            thrust_macros::assume!(|fields: &IndexSlice<FieldIdx, F>| <FieldIdx as Idx>::can_new((*fields).len()));
            #[cfg(thrust_ub_reach = "iter_enumerated")]
            thrust_macros::proof_assert!(|kind: StructKind| false);
            // Rewrite (rewrites.md R8): `Filter::new(it, p)` for `it.filter(p)`.
            // Fallback (open parts 36 to 39): `Filter::new` and `next` with their preconditions
            // assumed; restore `Filter::new` and `next` once the solver answers them.
            // Fallback (open part 61): `iter_enumerated` through the trusted
            // `iter_enumerated_trusted` of thrust/iter.rs; restore `fields.iter_enumerated()` once
            // the solver answers its body's goal at this call.
            let mut non_zst_fields = crate::case_study::iter::filter_new_assumed(crate::case_study::iter::iter_enumerated_trusted(fields), thrust_macros::closure!(
                requires(true),
                ensures(true),
                |&(_, f): &(FieldIdx, &F)| -> bool { !f.is_zst() },
            ));

            match (
                crate::case_study::iter::filter_next_assumed(&mut non_zst_fields),
                crate::case_study::iter::filter_next_assumed(&mut non_zst_fields),
                crate::case_study::iter::filter_next_assumed(&mut non_zst_fields),
            ) {
                (Some((i, field)), None, None) => {
                    layout_of_single_non_zst_field = Some(field);

                    // Assumed (fallback; open part 41, with fptprove): delete once the solver answers it.
                    // The index `offsets[i]`'s requires.
                    thrust_macros::assume!(|i: FieldIdx, offsets: &IndexVec<FieldIdx, Size>| <FieldIdx as crate::rustc_index::IntoSliceIdx<FieldIdx, [Size]>>::into_logic(i) < (*offsets).len());
                    #[cfg(thrust_ub_reach = "single_field")]
                    thrust_macros::proof_assert!(|kind: StructKind| false);
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
                        // A step of `scalar_pair`'s `requires`, before the order of the pair is
                        // chosen.
                        // Assumed (fallback; open part 42, the step's own goal, with fptprove): restore
                        // `proof_assert!` once the solver answers it.
                        thrust_macros::assume!(|a: Scalar, b: Scalar, self: &LayoutCalculator<Cx>|
                            forall(|d: TargetDataLayout| !Cx::dl_of(*self, d) || (Scalar::wf_in(a, d) && Scalar::wf_in(b, d))));
                        // Assumed (fallback; open parts 43 and 44, with fptprove): delete once the solver answers them.
                        // The indexes `offsets[i]` and `offsets[j]`'s requires.
                        thrust_macros::assume!(|i: FieldIdx, offsets: &IndexVec<FieldIdx, Size>| <FieldIdx as crate::rustc_index::IntoSliceIdx<FieldIdx, [Size]>>::into_logic(i) < (*offsets).len());
                        thrust_macros::assume!(|j: FieldIdx, offsets: &IndexVec<FieldIdx, Size>| <FieldIdx as crate::rustc_index::IntoSliceIdx<FieldIdx, [Size]>>::into_logic(j) < (*offsets).len());
                        #[cfg(thrust_ub_reach = "pair")]
                        thrust_macros::proof_assert!(|kind: StructKind| false);
                        let ((i, a), (j, b)) = if offsets[i] < offsets[j] {
                            ((i, a), (j, b))
                        } else {
                            ((j, b), (i, a))
                        };
                        // Assumed (fallback; open once the step above is assumed): delete once the
                        // solver answers it. `scalar_pair`'s requires, on the pair as ordered.
                        thrust_macros::assume!(|a: Scalar, b: Scalar, self: &LayoutCalculator<Cx>|
                            forall(|d: TargetDataLayout| !Cx::dl_of(*self, d) || (Scalar::wf_in(a, d) && Scalar::wf_in(b, d)))
                                && forall(|z: USize| z == 0usize ==> <VariantIdx as Idx>::can_new(z))
                                && forall(|k: USize| k == 0usize || k == 1usize ==> <FieldIdx as Idx>::can_new(k)));
                        let pair = LayoutData::<FieldIdx, VariantIdx>::scalar_pair(&self.cx, a, b);
                        // Assumed (fallback; open parts 46 and 47, with fptprove): delete once the solver answers them.
                        // The match's panicking arm is unreachable: `scalar_pair`'s `ensures` makes the fields `Arbitrary`.
                        thrust_macros::assume!(|pair: LayoutData<FieldIdx, VariantIdx>| matches!(pair.fields, FieldsShape::Arbitrary { .. }));
                        #[cfg(thrust_ub_reach = "scalar_pair")]
                        thrust_macros::proof_assert!(|kind: StructKind| false);
                        // Fallback (open parts 68 and 69): the match on the pair's fields through
                        // the trusted `arbitrary_parts` at the end of this file.
                        let pair_offsets = {
                            let (offsets, in_memory_order) = arbitrary_parts(&pair.fields);
                            // Assumed (fallback; open parts 48 and 49, with fptprove): delete once the solver answers them.
                            // `FieldIdx::new(0)` and `FieldIdx::new(1)`'s requires.
                            thrust_macros::assume!(|kind: StructKind| forall(|z: USize| z == 0usize ==> <FieldIdx as Idx>::can_new(z)));
                            thrust_macros::assume!(|kind: StructKind| forall(|z: USize| z == 1usize ==> <FieldIdx as Idx>::can_new(z)));
                            // Fallback: the expected order is bound to `expected` so that an
                            // `assume!` can state the comparison.
                            let expected = [FieldIdx::new(0), FieldIdx::new(1)];
                            // Assumed (fallback; open part 50, with fptprove): delete once the solver answers it.
                            // `assert_eq!`'s panic is unreachable.
                            thrust_macros::assume!(|in_memory_order: &IndexVec<u32, FieldIdx>, expected: [FieldIdx; 2]| *in_memory_order == expected);
                            assert_eq!(in_memory_order.raw, expected);
                            #[cfg(thrust_ub_reach = "arbitrary")]
                            thrust_macros::proof_assert!(|kind: StructKind| false);
                            offsets
                        };
                        // Assumed (fallback; open parts 51 to 56, with fptprove): delete once the solver answers them.
                        // The requires of the indexes and of `FieldIdx::new` in the condition below,
                        // which binds the two indices to `k0` and `k1` so that an `assume!` can state them.
                        thrust_macros::assume!(|i: FieldIdx, offsets: &IndexVec<FieldIdx, Size>| <FieldIdx as crate::rustc_index::IntoSliceIdx<FieldIdx, [Size]>>::into_logic(i) < (*offsets).len());
                        thrust_macros::assume!(|j: FieldIdx, offsets: &IndexVec<FieldIdx, Size>| <FieldIdx as crate::rustc_index::IntoSliceIdx<FieldIdx, [Size]>>::into_logic(j) < (*offsets).len());
                        thrust_macros::assume!(|kind: StructKind| forall(|z: USize| z == 0usize ==> <FieldIdx as Idx>::can_new(z)));
                        let k0 = FieldIdx::new(0);
                        thrust_macros::assume!(|kind: StructKind| forall(|z: USize| z == 1usize ==> <FieldIdx as Idx>::can_new(z)));
                        let k1 = FieldIdx::new(1);
                        thrust_macros::assume!(|k0: FieldIdx, pair_offsets: &IndexVec<FieldIdx, Size>| <FieldIdx as crate::rustc_index::IntoSliceIdx<FieldIdx, [Size]>>::into_logic(k0) < (*pair_offsets).len());
                        thrust_macros::assume!(|k1: FieldIdx, pair_offsets: &IndexVec<FieldIdx, Size>| <FieldIdx as crate::rustc_index::IntoSliceIdx<FieldIdx, [Size]>>::into_logic(k1) < (*pair_offsets).len());
                        #[cfg(thrust_ub_reach = "pair_condition")]
                        thrust_macros::proof_assert!(|kind: StructKind| false);
                        if offsets[i] == pair_offsets[k0]
                            && offsets[j] == pair_offsets[k1]
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
        let unadjusted_abi_align = if repr.transparent() {
            match layout_of_single_non_zst_field {
                Some(l) => l.unadjusted_abi_align,
                None => align,
            }
        } else {
            unadjusted_abi_align
        };
        (abi, unadjusted_abi_align)
    }

    /// Pads the offset to the field's alignment and raises the struct's alignment to it: the
    /// offset grows by less than the alignment's bytes, and the struct's alignment's bytes by at
    /// most them.
    #[thrust_macros::requires((*offset).raw <= 4611686018427387904u64)]
    #[thrust_macros::ensures((*offset).raw <= (!offset).raw && (!offset).raw < (*offset).raw + 9223372036854775808u64)]
    #[thrust_macros::ensures(forall(|q: USize, q2: USize, qa: USize|
        !(q == (*align).pow2 && q2 == (!align).pow2 && qa == field_align.abi.pow2)
        || ((!offset).raw < (*offset).raw + pow2(qa) && pow2(q2) <= pow2(q) + pow2(qa))))]
    fn align_step(offset: &mut Size, align: &mut Align, field_align: AbiAlign) {
        let aligned = (*offset).align_to(field_align.abi);
        thrust_macros::proof!(aligned_within(*offset, field_align.abi, aligned));
        thrust_macros::proof!(pow2_pos((*align).pow2 as u64));
        thrust_macros::proof!(pow2_pos(field_align.abi.pow2 as u64));
        *offset = aligned;
        *align = (*align).max(field_align.abi);
    }

    /// The write of a field's offset in `univariant_biased`'s field loop.
    #[thrust_macros::requires(forall(|j: USize| !<FieldIdx as Idx>::index_is(i, j) || j < (*offsets).len()))]
    #[thrust_macros::ensures((!offsets).len() == (*offsets).len())]
    #[thrust_macros::ensures(forall(|j: USize| !<FieldIdx as Idx>::index_is(i, j) || (!offsets)[j] == value))]
    #[thrust_macros::ensures(forall(|j: USize|
        !(0 <= j && j < (*offsets).len() && !<FieldIdx as Idx>::index_is(i, j)) || (!offsets)[j] == (*offsets)[j]))]
    fn set_offset<FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>>(
        offsets: &mut IndexVec<FieldIdx, Size>,
        i: FieldIdx,
        value: Size,
    ) {
        offsets[i] = value;
    }

    /// The niche choice of `univariant_biased`'s field loop for `field` placed at `offset`: the
    /// chosen niche ends by the field's end; it stays when the field has none and is never
    /// dropped, and with `End` the field's niche is taken while none has been.
    #[thrust_macros::requires(Self::deref_functional::<FieldIdx, VariantIdx, F>())]
    #[thrust_macros::requires(forall(|d: &&LayoutData<FieldIdx, VariantIdx>|
        !thrust_macros::post!(<F as core::ops::Deref>::deref(field), d) || Self::field_wf::<FieldIdx, VariantIdx>(**d, *dl)))]
    #[thrust_macros::requires(offset.raw < 13835058055282163712u64)]
    #[thrust_macros::requires(niche_ends_by(*largest_niche, *dl, offset))]
    #[thrust_macros::ensures(forall(|d: &&LayoutData<FieldIdx, VariantIdx>|
        !thrust_macros::post!(<F as core::ops::Deref>::deref(field), d)
            || niche_ends_by(!largest_niche, *dl, Size { raw: offset.raw + (**d).size.raw })))]
    #[thrust_macros::ensures((!largest_niche) == None
        ==> ((*largest_niche) == None && (!largest_niche_available) == (*largest_niche_available)))]
    #[thrust_macros::ensures((!largest_niche) == (*largest_niche)
        || exists(|d: &&LayoutData<FieldIdx, VariantIdx>, nn: Niche|
            thrust_macros::post!(<F as core::ops::Deref>::deref(field), d) && (**d).largest_niche == Some(nn)))]
    #[thrust_macros::ensures(forall(|d: &&LayoutData<FieldIdx, VariantIdx>, nn: Niche|
        !(thrust_macros::post!(<F as core::ops::Deref>::deref(field), d)
            && (**d).largest_niche == Some(nn)
            && matches!(*niche_bias, NicheBias::End)
            && *largest_niche_available == 0)
        || (!largest_niche) != None))]
    #[thrust::reveal(niche_ends_by, LayoutCalculator::field_wf)]
    fn offer_niche<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        largest_niche: &mut Option<Niche>,
        largest_niche_available: &mut u128,
        field: &F,
        offset: Size,
        niche_bias: &NicheBias,
        dl: &TargetDataLayout,
    ) {
        if let Some(mut niche) = field.largest_niche {
            let available = niche.available(dl);

            let prefer_new_niche = match niche_bias {
                NicheBias::Start => available > *largest_niche_available,

                NicheBias::End => available >= *largest_niche_available,
            };
            if prefer_new_niche {
                *largest_niche_available = available;
                niche.offset += offset;
                *largest_niche = Some(niche);
            }
        }
    }

    /// One pass of `univariant_biased`'s field loop over `field` at index `i`, after the unsized
    /// checks: its padding, the alignments, its offset, the niche it may offer and its size. The
    /// offset and the alignment's bytes grow by less than the field's weight, and the step fails
    /// only with `SizeOverflow`, when the padded field reaches the object size bound. The niche
    /// changes as `offer_niche` changes it.
    #[thrust_macros::requires(Self::deref_functional::<FieldIdx, VariantIdx, F>())]
    #[thrust_macros::requires(forall(|d: &&LayoutData<FieldIdx, VariantIdx>|
        !thrust_macros::post!(<F as core::ops::Deref>::deref(field), d) || Self::field_wf::<FieldIdx, VariantIdx>(**d, *dl)))]
    #[thrust_macros::requires((*dl).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*dl).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*dl).default_address_space_pointer_spec.pointer_size.raw == 8)]
    #[thrust_macros::requires((*offset).raw <= 4611686018427387904u64)]
    #[thrust_macros::requires(forall(|j: USize| !<FieldIdx as Idx>::index_is(i, j) || j < (*offsets).len()))]
    #[thrust_macros::requires(niche_ends_by(*largest_niche, *dl, *offset))]
    #[thrust_macros::ensures(result == Ok(()) || result == Err(LayoutCalculatorError::SizeOverflow))]
    #[thrust_macros::ensures(result == Ok(()) ==> ((!offset).raw < super::obj_bound(*dl) && niche_ends_by(!largest_niche, *dl, !offset)))]
    #[thrust_macros::ensures(forall(|d: &&LayoutData<FieldIdx, VariantIdx>, q: USize, q2: USize, qf: USize|
        !(result == Ok(())
            && thrust_macros::post!(<F as core::ops::Deref>::deref(field), d)
            && q == (*align).pow2 && q2 == (!align).pow2 && qf == (**d).align.abi.pow2)
        || (!offset).raw + pow2(q2) < (*offset).raw + pow2(q) + pow2(qf) * 2 + (**d).size.raw))]
    #[thrust_macros::ensures(forall(|d: &&LayoutData<FieldIdx, VariantIdx>, qf: USize|
        !(result == Err(LayoutCalculatorError::SizeOverflow)
            && thrust_macros::post!(<F as core::ops::Deref>::deref(field), d)
            && qf == (**d).align.abi.pow2)
        || (*offset).raw + pow2(qf) + (**d).size.raw > super::obj_bound(*dl)))]
    #[thrust_macros::ensures((!offsets).len() == (*offsets).len())]
    #[thrust_macros::ensures(forall(|j: USize|
        !(0 <= j && j < (*offsets).len() && !<FieldIdx as Idx>::index_is(i, j)) || (!offsets)[j] == (*offsets)[j]))]
    #[thrust_macros::ensures(forall(|j: USize, d: &&LayoutData<FieldIdx, VariantIdx>|
        !(result == Ok(())
            && <FieldIdx as Idx>::index_is(i, j)
            && thrust_macros::post!(<F as core::ops::Deref>::deref(field), d))
        || ((*offset).raw <= (!offsets)[j].raw && (!offsets)[j].raw + (**d).size.raw == (!offset).raw)))]
    #[thrust_macros::ensures((!largest_niche) == None
        ==> ((*largest_niche) == None && (!largest_niche_available) == (*largest_niche_available)))]
    #[thrust_macros::ensures((!largest_niche) == (*largest_niche)
        || exists(|d: &&LayoutData<FieldIdx, VariantIdx>, nn: Niche|
            thrust_macros::post!(<F as core::ops::Deref>::deref(field), d) && (**d).largest_niche == Some(nn)))]
    #[thrust_macros::ensures(forall(|d: &&LayoutData<FieldIdx, VariantIdx>, nn: Niche|
        !(thrust_macros::post!(<F as core::ops::Deref>::deref(field), d)
            && (**d).largest_niche == Some(nn)
            && matches!(*niche_bias, NicheBias::End)
            && *largest_niche_available == 0)
        || (!largest_niche) != None))]
    #[thrust::reveal(LayoutCalculator::field_wf)]
    fn place_field<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        offset: &mut Size,
        align: &mut Align,
        max_repr_align: &mut Option<Align>,
        offsets: &mut IndexVec<FieldIdx, Size>,
        i: FieldIdx,
        largest_niche: &mut Option<Niche>,
        largest_niche_available: &mut u128,
        field: &F,
        pack: Option<Align>,
        niche_bias: &NicheBias,
        dl: &TargetDataLayout,
    ) -> Result<(), LayoutCalculatorError<F>> {
        // The fail twin of the place_field root sets this cfg: the contract allows a field placed
        // at offset 0, so an assertion that the offset is not 0 is refuted.
        #[cfg(thrust_place_field_fail)]
        thrust_macros::proof_assert!(|offset: &mut Size| !((*offset).raw == 0));
        let field_align = if let Some(pack) = pack {
            field.align.min(AbiAlign::new(pack))
        } else {
            field.align
        };
        // `pack` only lowers the alignment, so its bytes stay within the field's.
        thrust_macros::proof!(pow2_mono(field_align.abi.pow2 as u64, field.align.abi.pow2 as u64));
        let before = *offset;
        Self::align_step(offset, align, field_align);
        thrust_macros::proof!(niche_ends_later(&*largest_niche, dl, before, *offset));
        *max_repr_align = (*max_repr_align).max(field.max_repr_align);

        // debug!("univariant offset: {:?} field: {:#?}", offset, field);
        Self::set_offset::<FieldIdx>(offsets, i, *offset);

        Self::offer_niche::<FieldIdx, VariantIdx, F>(largest_niche, largest_niche_available, field, *offset, niche_bias, dl);

        *offset = (*offset)
            .checked_add(field.size, dl)
            .ok_or(LayoutCalculatorError::SizeOverflow)?;
        thrust_macros::proof_assert!(|largest_niche: &mut Option<Niche>, dl: &TargetDataLayout, offset: &mut Size|
            niche_ends_by(*largest_niche, *dl, *offset));
        Ok(())
    }

    /// `univariant_biased`'s field loop (rewrites.md R19): places the fields in `in_memory_order`
    /// after `offset` and returns the unsized tail of a `MaybeUnsized` struct, if any. It fails
    /// with `UnexpectedUnsized` exactly when an unsized field is misplaced, unless it fails with
    /// `SizeOverflow` first, and with `SizeOverflow` only when the fields' weight from `offset`
    /// and the alignment's bytes reaches the object size bound; the offset and the alignment's
    /// bytes grow by at most the fields' weight. With `Start` a niche comes from some field's, and
    /// with `End` any field's niche gives one.
    #[thrust_macros::requires(Self::deref_functional::<FieldIdx, VariantIdx, F>())]
    #[thrust_macros::requires((*dl).default_address_space_pointer_spec.pointer_size.raw == 2
        || (*dl).default_address_space_pointer_spec.pointer_size.raw == 4
        || (*dl).default_address_space_pointer_spec.pointer_size.raw == 8)]
    #[thrust_macros::requires(Self::fields_ok::<FieldIdx, VariantIdx, F>(fields, *dl))]
    #[thrust_macros::requires(Self::order_ok::<FieldIdx>(*in_memory_order, (*fields).len(), kind))]
    #[thrust_macros::requires((*offsets).len() == (*fields).len())]
    #[thrust_macros::requires((*offset).raw <= 4611686018427387904u64)]
    #[thrust_macros::requires(*largest_niche == None && *largest_niche_available == 0)]
    #[thrust_macros::ensures(forall(|e: LayoutCalculatorError<<F as thrust_models::Model>::Ty>|
        result != Err(e)
            || e == LayoutCalculatorError::SizeOverflow
            || exists(|f: <F as thrust_models::Model>::Ty| e == LayoutCalculatorError::UnexpectedUnsized(f))))]
    #[thrust_macros::ensures((!offsets).len() == (*offsets).len())]
    #[thrust_macros::ensures(
        (exists(|f: <F as thrust_models::Model>::Ty| result == Err(LayoutCalculatorError::UnexpectedUnsized(f)))
            ==> Self::unsized_misplaced::<FieldIdx, VariantIdx, F>(fields, kind))
        && (Self::unsized_misplaced::<FieldIdx, VariantIdx, F>(fields, kind)
            ==> (exists(|f: <F as thrust_models::Model>::Ty| result == Err(LayoutCalculatorError::UnexpectedUnsized(f)))
                || result == Err(LayoutCalculatorError::SizeOverflow))))]
    #[thrust_macros::ensures(forall(|u: Option<&<F as thrust_models::Model>::Ty>| result == Ok(u)
        ==> ((!offset).raw <= 4611686018427387904u64 && niche_ends_by(!largest_niche, *dl, !offset))))]
    #[thrust_macros::ensures(forall(|u: Option<&<F as thrust_models::Model>::Ty>, ts: Seq<Int>, q: USize, q0: USize|
        !(result == Ok(u) && Self::weights_are::<FieldIdx, VariantIdx, F>(fields, ts) && q == (!align).pow2 && q0 == (*align).pow2)
        || (!offset).raw + pow2(q) <= (*offset).raw + pow2(q0) + sum_first(ts, (*fields).len())))]
    #[thrust_macros::ensures(forall(|ts: Seq<Int>, q0: USize|
        !(Self::weights_are::<FieldIdx, VariantIdx, F>(fields, ts)
            && q0 == (*align).pow2
            && (*offset).raw + pow2(q0) + sum_first(ts, (*fields).len()) <= super::obj_bound(*dl))
        || result != Err(LayoutCalculatorError::SizeOverflow)))]
    #[thrust_macros::ensures((!largest_niche) != None ==> Self::some_field_niche::<FieldIdx, VariantIdx, F>(fields))]
    #[thrust_macros::ensures(forall(|u: Option<&<F as thrust_models::Model>::Ty>|
        !(result == Ok(u) && matches!(*niche_bias, NicheBias::End) && Self::some_field_niche::<FieldIdx, VariantIdx, F>(fields))
        || (!largest_niche) != None))]
    #[thrust::reveal(
        LayoutCalculator::field_wf,
        LayoutCalculator::unsized_misplaced,
        LayoutCalculator::some_field_niche
    )]
    fn place_fields<
        'a,
        'b,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model<Ty: PartialEq>,
    >(
        fields: &'b IndexSlice<FieldIdx, F>,
        in_memory_order: &IndexVec<u32, FieldIdx>,
        kind: StructKind,
        pack: Option<Align>,
        niche_bias: &NicheBias,
        dl: &TargetDataLayout,
        offsets: &mut IndexVec<FieldIdx, Size>,
        offset: &mut Size,
        align: &mut Align,
        max_repr_align: &mut Option<Align>,
        largest_niche: &mut Option<Niche>,
        largest_niche_available: &mut u128,
    ) -> Result<Option<&'b F>, LayoutCalculatorError<F>> {
        let order = thrust_macros::ghost!(|in_memory_order: &IndexVec<u32, FieldIdx>| -> IndexVec<u32, FieldIdx> {
            *in_memory_order
        });
        thrust_macros::proof!(sum_at_le(order, fields.len()));
        thrust_macros::proof!(no_niche_ends_by(dl, *offset));
        // The fail twin of the place_fields root sets this cfg: the invariant lets the loop move
        // the offset, so an assertion that it ends where it started is refuted.
        #[cfg(thrust_place_fields_fail)]
        let offset_before = thrust_macros::ghost!(|offset: &mut Size| -> Size { *offset });
        // The loop's invariant names the entry values of `offset` and `align` by the parameters.
        let (next_offset, struct_align) = (offset, align);
        let mut unsized_field = None::<&F>;
        for &i in in_memory_order {
            thrust_macros::invariant!(
                |iter: crate::rustc_index::SliceIter<'_, FieldIdx>,
                 iter_old: thrust_models::Ghost<crate::rustc_index::SliceIter<'_, FieldIdx>>,
                 produced: thrust_models::Ghost<Seq<&<FieldIdx as thrust_models::Model>::Ty>>,
                 in_memory_order: thrust_models::FnParam<&IndexVec<u32, FieldIdx>>,
                 offset: thrust_models::FnParam<&mut Size>,
                 align: thrust_models::FnParam<&mut Align>,
                 fields: &IndexSlice<FieldIdx, F>,
                 kind: StructKind,
                 niche_bias: &NicheBias,
                 dl: &TargetDataLayout,
                 offsets: &mut IndexVec<FieldIdx, Size>,
                 next_offset: &mut Size,
                 struct_align: &mut Align,
                 largest_niche: &mut Option<Niche>,
                 largest_niche_available: &mut u128,
                 unsized_field: Option<&F>| {
                    *iter_old.0 == *in_memory_order.at_entry()
                        && iter_old.1 == 0
                        && !next_offset == !offset.at_entry()
                        && !struct_align == !align.at_entry()
                        && Self::deref_functional::<FieldIdx, VariantIdx, F>()
                        && ((*dl).default_address_space_pointer_spec.pointer_size.raw == 2
                            || (*dl).default_address_space_pointer_spec.pointer_size.raw == 4
                            || (*dl).default_address_space_pointer_spec.pointer_size.raw == 8)
                        && Self::fields_ok::<FieldIdx, VariantIdx, F>(fields, *dl)
                        && Self::order_ok::<FieldIdx>(*in_memory_order.at_entry(), (*fields).len(), kind)
                        && forall(|ts: Seq<Int>, k: USize|
                            !(0 <= k && k <= (*fields).len() && forall(|i: USize| !(0 <= i && i < (*fields).len()) || ts[i] >= 0))
                                || sum_at::<FieldIdx>(ts, *in_memory_order.at_entry(), k) <= sum_first(ts, (*fields).len()))
                        && (*offsets).len() == (*fields).len()
                        && (*next_offset).raw <= 4611686018427387904u64
                        && niche_ends_by(*largest_niche, *dl, *next_offset)
                        && forall(|ts: Seq<Int>, q: USize, q0: USize|
                            !(Self::weights_are::<FieldIdx, VariantIdx, F>(fields, ts) && q == (*struct_align).pow2 && q0 == (*align.at_entry()).pow2)
                                || (*next_offset).raw + pow2(q) <= (*offset.at_entry()).raw + pow2(q0) + sum_at::<FieldIdx>(ts, *in_memory_order.at_entry(), produced.len()))
                        && (*largest_niche != None || *largest_niche_available == 0)
                        && (*largest_niche == None || Self::some_field_niche::<FieldIdx, VariantIdx, F>(fields))
                        && (!(matches!(*niche_bias, NicheBias::End) && *largest_niche == None)
                            || forall(|j: USize, i: USize, d: &&LayoutData<FieldIdx, VariantIdx>|
                                !(0 <= j && j < produced.len() && i == <FieldIdx as Idx>::index_logic((*in_memory_order.at_entry())[j])
                                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d))
                                    || (**d).largest_niche == None))
                        && (unsized_field != None
                            || forall(|j: USize, i: USize, d: &&LayoutData<FieldIdx, VariantIdx>|
                                !(0 <= j && j < produced.len() && i == <FieldIdx as Idx>::index_logic((*in_memory_order.at_entry())[j])
                                    && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d))
                                    || (**d).backend_repr != BackendRepr::Memory { sized: false }))
                        && (unsized_field == None
                            || (matches!(kind, StructKind::MaybeUnsized)
                                && produced.len() >= 1
                                && forall(|j: USize, i: USize, d: &&LayoutData<FieldIdx, VariantIdx>|
                                    !(0 <= j && j < produced.len() && i == <FieldIdx as Idx>::index_logic((*in_memory_order.at_entry())[j])
                                        && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d))
                                        || (j + 1 == produced.len()) == ((**d).backend_repr == BackendRepr::Memory { sized: false }))))
                }
            );
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

            thrust_macros::proof!(niche_sized(field.largest_niche, dl, dl.address_space_info.len()));
            thrust_macros::proof!(pow2_pos((*struct_align).pow2 as u64));
            // Rewrite (rewrites.md R18): the rest of the body as `place_field`.
            Self::place_field::<FieldIdx, VariantIdx, F>(
                next_offset,
                struct_align,
                max_repr_align,
                offsets,
                i,
                largest_niche,
                largest_niche_available,
                field,
                pack,
                niche_bias,
                dl,
            )?;
        }
        #[cfg(thrust_place_fields_fail)]
        thrust_macros::proof_assert!(|next_offset: &mut Size, offset_before: thrust_models::Ghost<Size>|
            (*next_offset).raw == offset_before.raw);
        Ok(unsized_field)
    }
}

// Fallback (open parts 68 and 69 of `univariant_biased`): the match on a scalar pair's fields there,
// trusted on its contract. The solver does not answer that its panicking arm is unreachable, even
// right after the `assume!` that the fields are `Arbitrary`. The contract is what the match does:
// it panics unless the fields are `Arbitrary`, and gives their offsets and memory order.
#[thrust::trusted]
#[thrust_macros::requires(matches!(*fields, FieldsShape::Arbitrary { .. }))]
#[thrust_macros::ensures(exists(|o: IndexVec<FieldIdx, Size>, m: IndexVec<u32, FieldIdx>,
        os: Seq<Size>, ms: Seq<<FieldIdx as thrust_models::Model>::Ty>|
    *fields == FieldsShape::Arbitrary { offsets: o, in_memory_order: m }
        && os == o
        && ms == m
        && *result.0 == os
        && *result.1 == ms))]
fn arbitrary_parts<FieldIdx: Idx + thrust_models::Model>(
    fields: &FieldsShape<FieldIdx>,
) -> (&IndexVec<FieldIdx, Size>, &IndexVec<u32, FieldIdx>) {
    match fields {
        FieldsShape::Arbitrary {
            offsets,
            in_memory_order,
        } => (offsets, in_memory_order),
        FieldsShape::Primitive | FieldsShape::Array { .. } | FieldsShape::Union(..) => {
            panic!("encountered a non-arbitrary layout during enum layout")
        }
    }
}

// Returns its argument. A reference copied from a closure's capture with `let` is folded into the
// capture's place in the MIR Thrust reads, where an `assume!` cannot name it; the result of this
// call is a local of its own.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn as_local<T: thrust_models::Model>(x: T) -> T {
    x
}
