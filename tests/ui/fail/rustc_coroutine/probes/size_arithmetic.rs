//@no-rustfix
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=field_niche_placed,rustc_abi::Size::add_assign,rustc_abi::Size::bits,rustc_abi::Niche::available THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1

// The size arithmetic of layout.rs's `univariant_biased` over the case study's `Size`, `Align`,
// `Niche` and `TargetDataLayout`: `Size::align_to` (the prefix, each field, the final padding),
// `Size::checked_add` against `obj_size_bound`, and the niche choice with `Niche::available` and
// the niche's move by the field's offset. `univariant_size` states the size clauses of
// `univariant_biased`'s contract: an `Ok` layout's size is below the weight `s` of layout.rs's
// `weighs` and its alignment at most `s`, `SizeOverflow` never when `s` is below the object size
// bound, and the niche lies within the size. The copies of `Align::bytes`, `align_to`,
// `obj_size_bound` and `checked_add` carry the contracts the case study's do not (there
// `Align::bytes` has none, `align_to` is `#[thrust::callable]`, and `obj_size_bound` and
// `checked_add` ensure only `result >= 1` and `true`); the loop's body, the prefix and the
// final padding are helpers with written contracts (`place_field`, `place_prefix`, `finish`). The
// requires add to layout.rs's `layout_pre` what the arithmetic needs (`field_wf`, `prefix_weighs`,
// `repr_weighs`, `dl_wf`): sizes below the object size bound, alignments at most `Align::MAX`, and
// a niche offset within the field.
// The fail twin: `field_wf` leaves out the niche offset's bound, which `layout_pre` also lacks (it
// bounds the niche's end only for the sizes `Primitive::size_in` allows). `field_niche_placed`,
// which hands `offer_niche` that bound for `niche.offset += offset` (`Size::add` panics on
// overflow), is refuted; only it is verified.

#![feature(new_range_api)]

#[path = "../../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use thrust_models::model::{BitVec, Int, Seq};
use thrust_models::{exists, forall, FnParam, Ghost};

use case_study::USize;

use rustc_abi::{AbiAlign, Align, Niche, Primitive, ReprOptions, Size, StructKind, TargetDataLayout};

/// `2^q`, the bytes of `Align { pow2: q }`: layout.rs's `pow2`.
#[thrust_macros::logic]
#[thrust_macros::variant(q)]
fn pow2(q: u64) -> u64 {
    if q <= 0 { 1 } else { pow2(q - 1) * 2 }
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

/// An alignment up to `Align::MAX` has at most its bytes.
#[thrust_macros::lemma]
#[thrust_macros::ensures(q <= 29 ==> pow2(q) <= 536870912)]
fn pow2_max(q: u64) {
    if q <= 29 {
        pow2_mono(q, 29);
    }
}

/// `1 << q` on 64-bit words is `2^q` below 64, by induction over `q`.
#[thrust_macros::lemma]
#[thrust_macros::variant(q)]
#[thrust_macros::requires(q < 64)]
#[thrust_macros::ensures(pow2(q)
    == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int())]
fn shl_is_pow2(q: u64) {
    if q > 0 {
        shl_is_pow2(q - 1);
    }
}

/// `Align::bytes`: `1 << pow2`, the shift amount masked to the width.
#[thrust_macros::requires(a.pow2 < 64)]
#[thrust_macros::ensures(forall(|q: USize| q == a.pow2 ==> result == pow2(q)))]
#[thrust_macros::ensures(result
    == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(a.pow2) & BitVec::from_int(63))).to_int())]
fn align_bytes(a: Align) -> u64 {
    thrust_macros::proof!(shl_is_pow2(a.pow2 as u64));
    1 << a.pow2
}

/// Rounding `x` up with the mask `m` of a power of two: unless `x + m` wraps, `(x + m) & !m`
/// lies in `[x, x + m]`.
#[thrust_macros::lemma]
#[thrust_macros::requires(q < 64)]
#[thrust_macros::requires(m + 1
    == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int())]
#[thrust_macros::ensures(x + m <= u64::MAX
    ==> (x <= (BitVec::<64, false>::from_int(x + m) & !BitVec::<64, false>::from_int(m)).to_int()
        && (BitVec::<64, false>::from_int(x + m) & !BitVec::<64, false>::from_int(m)).to_int() <= x + m))]
fn round_up(x: u64, m: u64, q: u64) {}

/// `Size::align_to`: the least multiple of the alignment at or above `x`, when `x` plus the
/// alignment's mask does not wrap.
#[thrust_macros::requires(a.pow2 < 64)]
#[thrust_macros::ensures(forall(|q: USize| q == a.pow2 && x.raw + pow2(q) - 1 <= u64::MAX
    ==> (x.raw <= result.raw && result.raw < x.raw + pow2(q))))]
#[thrust_macros::ensures(forall(|q: USize| q == a.pow2 && q <= 29 ==> pow2(q) <= 536870912))]
fn align_to(x: Size, a: Align) -> Size {
    thrust_macros::proof!(pow2_max(a.pow2 as u64));
    let mask = align_bytes(a) - 1;
    thrust_macros::proof!(round_up(x.bytes(), mask, a.pow2 as u64));
    Size::from_bytes((x.bytes() + mask) & !mask)
}

/// The sum of the first `k` entries of `ts`: layout.rs's `sum_first`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn sum_first(ts: Seq<Int>, k: USize) -> Int {
    if k <= 0 { 0 } else { sum_first(ts, k - 1) + ts[k - 1] }
}

/// `obj_size_bound` of a layout whose default pointer has 2, 4 or 8 bytes.
#[thrust_macros::logic]
fn obj_bound(dl: TargetDataLayout) -> u64 {
    if dl.default_address_space_pointer_spec.pointer_size.raw == 2 {
        32768
    } else if dl.default_address_space_pointer_spec.pointer_size.raw == 4 {
        2147483648
    } else {
        2305843009213693952
    }
}

/// The default pointer has 2, 4 or 8 bytes (layout.rs's `layout_pre`), and the data layout's
/// alignments are at most `Align::MAX`.
#[thrust_macros::predicate]
#[thrust::opaque]
fn dl_wf(dl: TargetDataLayout) -> bool {
    (dl.default_address_space_pointer_spec.pointer_size.raw == 2
        || dl.default_address_space_pointer_spec.pointer_size.raw == 4
        || dl.default_address_space_pointer_spec.pointer_size.raw == 8)
        && dl.aggregate_align.pow2 <= 29
        && dl.i8_align.pow2 <= 29
}

/// `Niche::wf_in` of a niche of the primitive `value`: what `Niche::available` requires of the
/// niche under `dl`.
#[thrust_macros::predicate]
#[thrust::opaque]
fn niche_wf(value: Primitive, dl: TargetDataLayout) -> bool {
    forall(|a: rustc_abi::AddressSpace| !(value == Primitive::Pointer(a))
        || (TargetDataLayout::pointer_space_ok(dl, a)
            && forall(|m: Size| !TargetDataLayout::pointer_size_is(dl, a, m) || m.raw * 8 <= 128)))
}

/// `niche_wf`'s definition, in the form `Niche::available`'s `requires` states it.
#[thrust_macros::lemma]
#[thrust_macros::requires(niche_wf(value, *dl))]
#[thrust_macros::ensures(forall(|a: rustc_abi::AddressSpace| value == Primitive::Pointer(a)
    ==> (TargetDataLayout::pointer_space_ok(*dl, a)
        && forall(|m: Size| TargetDataLayout::pointer_size_is(*dl, a, m) ==> m.raw * 8 <= 128))))]
#[thrust::reveal(niche_wf)]
fn niche_wf_unfold(value: Primitive, dl: &TargetDataLayout) {}

/// `TargetDataLayout::obj_size_bound`.
#[thrust_macros::requires(dl_wf(*dl))]
#[thrust_macros::ensures(result == obj_bound(*dl))]
#[thrust::reveal(dl_wf)]
fn obj_size_bound(dl: &TargetDataLayout) -> u64 {
    match dl.pointer_size().bits() {
        16 => 1 << 15,
        32 => 1 << 31,
        64 => 1 << 61,
        bits => panic!("obj_size_bound: unknown pointer bit size {bits}"),
    }
}

/// `Size::checked_add`: the sum when it is below the object size bound.
#[thrust_macros::requires(dl_wf(*dl))]
#[thrust_macros::ensures(forall(|z: Size| result == Some(z)
    ==> (z.raw == this.raw + offset.raw && z.raw < obj_bound(*dl))))]
#[thrust_macros::ensures(result == None ==> this.raw + offset.raw >= obj_bound(*dl))]
fn checked_add(this: Size, offset: Size, dl: &TargetDataLayout) -> Option<Size> {
    let bytes = this.bytes().checked_add(offset.bytes())?;

    if bytes < obj_size_bound(dl) {
        Some(Size::from_bytes(bytes))
    } else {
        None
    }
}

/// The parts of a field's `LayoutData` that the size arithmetic reads.
#[derive(Clone, Copy, PartialEq, Eq)]
struct FieldLayout {
    size: Size,
    align: AbiAlign,
    largest_niche: Option<Niche>,
}

impl thrust_models::Model for FieldLayout {
    type Ty = Self;
}

/// The size, alignment and niche `univariant_biased` puts in its `LayoutData`.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Placed {
    size: Size,
    align: Align,
    largest_niche: Option<Niche>,
}

impl thrust_models::Model for Placed {
    type Ty = Self;
}

/// The error of `univariant_biased`'s size arithmetic: `LayoutCalculatorError::SizeOverflow`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LayoutError {
    SizeOverflow,
}

impl thrust_models::Model for LayoutError {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum NicheBias {
    Start,
    End,
}

impl thrust_models::Model for NicheBias {
    type Ty = Self;
}

/// An invariant of the layouts rustc computes: the field's alignment is at most `Align::MAX`,
/// its size is below the object size bound, and its niche is well formed and lies within it
/// (layout.rs's `layout_pre` states the last two, the niche's extent only for the sizes
/// `Primitive::size_in` allows, which leaves the niche's offset unbounded where it allows none).
#[thrust_macros::predicate]
#[thrust::opaque]
fn field_wf(f: FieldLayout, dl: TargetDataLayout) -> bool {
    f.align.abi.pow2 <= 29
        && f.size.raw < obj_bound(dl)
        && forall(|n: Niche, s: Size| !(f.largest_niche == Some(n))
            || (niche_wf(n.value, dl)
                && (!Primitive::size_in(n.value, dl, s) || n.offset.raw + s.raw <= f.size.raw)))
}

#[thrust_macros::predicate]
#[thrust::opaque]
fn fields_wf(fields: &[FieldLayout], dl: TargetDataLayout) -> bool {
    forall(|i: Int| !(0 <= i && i < (*fields).len()) || field_wf((*fields)[i], dl))
}

/// `ts` holds each field's size and twice its alignment: the witness of layout.rs's `weight`.
#[thrust_macros::predicate]
#[thrust::opaque]
fn weights(fields: &[FieldLayout], ts: Seq<Int>) -> bool {
    ts.len() == (*fields).len()
        && forall(|i: Int, q: USize| !(0 <= i && i < ts.len() && q == (*fields)[i].align.abi.pow2)
            || ts[i] == pow2(q) * 2 + (*fields)[i].size.raw)
}

/// The weights' partial sums grow with the number of fields summed.
#[thrust_macros::lemma]
#[thrust_macros::variant(n)]
#[thrust_macros::requires(weights(fields, ts) && k <= n && n <= ts.len())]
#[thrust_macros::ensures(sum_first(ts, k) <= sum_first(ts, n))]
#[thrust::reveal(weights)]
fn sum_first_mono(fields: &[FieldLayout], ts: Ghost<Seq<Int>>, k: usize, n: usize) {
    if k < n {
        sum_first_mono(fields, ts, k, n - 1);
    }
}

/// The weight of field `k`: the step the offset loop's bound takes there, within the total.
#[thrust_macros::lemma]
#[thrust_macros::requires(weights(fields, ts) && k < (*fields).len())]
#[thrust_macros::ensures(forall(|qf: USize| qf == (*fields)[k].align.abi.pow2
    ==> (sum_first(ts, k + 1) == sum_first(ts, k) + pow2(qf) * 2 + (*fields)[k].size.raw
        && sum_first(ts, k + 1) <= sum_first(ts, ts.len()))))]
#[thrust::reveal(weights)]
fn weight_step(fields: &[FieldLayout], ts: Ghost<Seq<Int>>, k: usize) {
    sum_first_mono(fields, ts, k + 1, (*fields).len());
}

/// The invariant of field `k`.
#[thrust_macros::lemma]
#[thrust_macros::requires(fields_wf(fields, *dl) && k < (*fields).len())]
#[thrust_macros::ensures(field_wf((*fields)[k], *dl))]
#[thrust::reveal(fields_wf)]
fn field_at(fields: &[FieldLayout], dl: &TargetDataLayout, k: usize) {}

/// `p` is the prefix's size and twice its alignment, 0 without a prefix (layout.rs's `weighs`);
/// the prefix is below the object size bound and its alignment at most `Align::MAX`.
#[thrust_macros::predicate]
#[thrust::opaque]
fn prefix_weighs(kind: StructKind, dl: TargetDataLayout, p: Int) -> bool {
    (forall(|ps: Size, pa: Align| kind != StructKind::Prefixed(ps, pa)) && p == 0)
        || exists(|ps: Size, pa: Align, q: USize| kind == StructKind::Prefixed(ps, pa)
            && q == pa.pow2
            && pa.pow2 <= 29
            && ps.raw < obj_bound(dl)
            && p == pow2(q) * 2 + ps.raw)
}

/// `r` is the `repr` alignment's bytes, 0 without one (layout.rs's `weighs`); the alignment is
/// at most `Align::MAX`.
#[thrust_macros::predicate]
#[thrust::opaque]
fn repr_weighs(repr: ReprOptions, r: Int) -> bool {
    ((repr.align == None && r == 0)
        || exists(|ra: Align, q: USize| repr.align == Some(ra) && q == ra.pow2 && ra.pow2 <= 29 && r == pow2(q)))
}

/// `s` bounds every order of the fields: their weight, the prefix's, the `repr` alignment and
/// the aggregate and `i8` alignments of `dl` (layout.rs's `weighs`).
#[thrust_macros::predicate]
fn weighs(ts: Seq<Int>, p: Int, r: Int, dl: TargetDataLayout, s: Int) -> bool {
    exists(|qa: USize, qi: USize| qa == dl.aggregate_align.pow2
        && qi == dl.i8_align.pow2
        && s == sum_first(ts, ts.len()) + p + r + pow2(qa) + pow2(qi))
}

/// `niche`, if any, is well formed and ends at or before `end`.
#[thrust_macros::predicate]
#[thrust::opaque]
fn niche_ends_by(niche: Option<Niche>, dl: TargetDataLayout, end: Size) -> bool {
    forall(|n: Niche, s: Size| !(niche == Some(n))
        || (niche_wf(n.value, dl) && (!Primitive::size_in(n.value, dl, s) || n.offset.raw + s.raw <= end.raw)))
}

/// No niche ends by any end.
#[thrust_macros::lemma]
#[thrust_macros::ensures(niche_ends_by(None, *dl, end))]
#[thrust::reveal(niche_ends_by)]
fn no_niche_ends(dl: &TargetDataLayout, end: Size) {}

/// A niche that ends by `end` ends by any later end.
#[thrust_macros::lemma]
#[thrust_macros::requires(end.raw <= later.raw && niche_ends_by(*niche, *dl, end))]
#[thrust_macros::ensures(niche_ends_by(*niche, *dl, later))]
#[thrust::reveal(niche_ends_by)]
fn niche_ends_later(niche: &Option<Niche>, dl: &TargetDataLayout, end: Size, later: Size) {}

/// A niche that ends by `end` ends by `end` plus `len`.
#[thrust_macros::lemma]
#[thrust_macros::requires(niche_ends_by(*niche, *dl, end))]
#[thrust_macros::ensures(niche_ends_by(*niche, *dl, Size { raw: end.raw + len.raw }))]
#[thrust::reveal(niche_ends_by)]
fn niche_ends_past(niche: &Option<Niche>, dl: &TargetDataLayout, end: Size, len: Size) {}

/// The niche of a field placed at `offset`, moved by it: well formed, and it ends by the field's
/// end. Its offset before the move is at most the field's size.
#[thrust_macros::lemma]
#[thrust_macros::requires(field_wf(*f, *dl) && (*f).largest_niche == Some(n))]
#[thrust_macros::ensures(n.offset.raw <= (*f).size.raw && (*f).size.raw < obj_bound(*dl) && niche_wf(n.value, *dl))]
#[thrust_macros::ensures(niche_ends_by(Some(Niche { offset: Size { raw: n.offset.raw + offset.raw }, value: n.value, valid_range: n.valid_range }),
    *dl, Size { raw: offset.raw + (*f).size.raw }))]
#[thrust::reveal(niche_ends_by, field_wf)]
fn field_niche_placed(f: &FieldLayout, n: Niche, dl: &TargetDataLayout, offset: Size) {} //~ ERROR: Unsat

/// The field's alignment, lowered to `pack` if there is one.
#[thrust_macros::requires((*field_align).abi.pow2 <= 29)]
#[thrust_macros::ensures(result.abi.pow2 <= (*field_align).abi.pow2)]
#[thrust_macros::ensures(forall(|q: USize, qf: USize| !(q == result.abi.pow2 && qf == (*field_align).abi.pow2)
    || pow2(q) <= pow2(qf)))]
fn packed_align(field_align: &AbiAlign, pack: Option<Align>) -> AbiAlign {
    if let Some(pack) = pack {
        let packed = field_align.min(AbiAlign::new(pack));
        thrust_macros::proof!(pow2_mono(packed.abi.pow2 as u64, field_align.abi.pow2 as u64));
        packed
    } else {
        *field_align
    }
}

/// The niche choice of the offset loop for `field` placed at `offset`: the chosen niche ends by
/// the field's end.
#[thrust_macros::requires(dl_wf(*dl) && field_wf(*field, *dl) && offset.raw <= 4611686018964258816u64)]
#[thrust_macros::requires(niche_ends_by(*largest_niche, *dl, offset))]
#[thrust_macros::ensures(niche_ends_by(!largest_niche, *dl, Size { raw: offset.raw + (*field).size.raw }))]
fn offer_niche(
    largest_niche: &mut Option<Niche>,
    largest_niche_available: &mut u128,
    field: &FieldLayout,
    offset: Size,
    niche_bias: NicheBias,
    dl: &TargetDataLayout,
) {
    thrust_macros::proof!(niche_ends_past(&*largest_niche, dl, offset, field.size));
    if let Some(mut niche) = field.largest_niche {
        thrust_macros::proof!(field_niche_placed(field, niche, dl, offset));
        thrust_macros::proof!(niche_wf_unfold(niche.value, dl));
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

/// One pass of `univariant_biased`'s offset loop over `field`: its padding, the alignment, the
/// niche it may offer and its size. The offset and the alignment's bytes grow by less than the
/// field's weight, and the step fails only when the padded field reaches the object size bound.
#[thrust_macros::requires(dl_wf(*dl) && field_wf(*field, *dl))]
#[thrust_macros::requires((*align).pow2 <= 29 && (*offset).raw <= 4611686018427387904u64)]
#[thrust_macros::requires(niche_ends_by(*largest_niche, *dl, *offset))]
#[thrust_macros::ensures((!align).pow2 <= 29)]
#[thrust_macros::ensures(result == Ok(()) ==> ((!offset).raw < obj_bound(*dl) && niche_ends_by(!largest_niche, *dl, !offset)))]
#[thrust_macros::ensures(forall(|q: USize, q2: USize, qf: USize| !(result == Ok(())
        && q == (*align).pow2 && q2 == (!align).pow2 && qf == (*field).align.abi.pow2)
    || (!offset).raw + pow2(q2) < (*offset).raw + pow2(q) + pow2(qf) * 2 + (*field).size.raw))]
#[thrust_macros::ensures(forall(|qf: USize| !(result == Err(LayoutError::SizeOverflow) && qf == (*field).align.abi.pow2)
    || (*offset).raw + pow2(qf) + (*field).size.raw > obj_bound(*dl)))]
#[thrust::reveal(field_wf)]
fn place_field(
    offset: &mut Size,
    align: &mut Align,
    largest_niche: &mut Option<Niche>,
    largest_niche_available: &mut u128,
    field: &FieldLayout,
    pack: Option<Align>,
    niche_bias: NicheBias,
    dl: &TargetDataLayout,
) -> Result<(), LayoutError> {
    let field_align = packed_align(&field.align, pack);
    let aligned = align_to(*offset, field_align.abi);
    thrust_macros::proof!(niche_ends_later(&*largest_niche, dl, *offset, aligned));
    *offset = aligned;
    *align = (*align).max(field_align.abi);

    offer_niche(largest_niche, largest_niche_available, field, *offset, niche_bias, dl);

    *offset = checked_add(*offset, field.size, dl).ok_or(LayoutError::SizeOverflow)?;
    Ok(())
}

/// The offset and the alignment after the prefix of a `Prefixed` struct, from the aggregate or
/// `i8` alignment: the offset and the alignment's bytes stay within the prefix's weight `p` and
/// the two alignments' bytes.
#[thrust_macros::requires(dl_wf(*dl) && prefix_weighs(kind, *dl, p))]
#[thrust_macros::requires(*align == (*dl).i8_align || *align == (*dl).aggregate_align)]
#[thrust_macros::ensures((!align).pow2 <= 29 && result.raw <= 4611686018427387904u64)]
#[thrust_macros::ensures(forall(|q2: USize, qa: USize, qi: USize| !(q2 == (!align).pow2
        && qa == (*dl).aggregate_align.pow2 && qi == (*dl).i8_align.pow2)
    || result.raw + pow2(q2) <= p + pow2(qa) + pow2(qi)))]
#[thrust::reveal(dl_wf, prefix_weighs)]
fn place_prefix(
    kind: StructKind,
    pack: Option<Align>,
    align: &mut Align,
    dl: &TargetDataLayout,
    p: Ghost<Int>,
) -> Size {
    let mut offset = Size::ZERO;
    if let StructKind::Prefixed(prefix_size, prefix_align) = kind {
        let prefix_align = if let Some(pack) = pack {
            let packed = prefix_align.min(pack);
            thrust_macros::proof!(pow2_mono(packed.pow2 as u64, prefix_align.pow2 as u64));
            packed
        } else {
            prefix_align
        };
        *align = (*align).max(prefix_align);
        offset = align_to(prefix_size, prefix_align);
    }
    offset
}

/// The end of `univariant_biased` after the offset loop: the `repr` alignment, the final
/// padding and the object size bound. The size stays below the offset plus the alignment's and
/// the `repr` alignment's bytes `r`, and the chosen niche lies within it.
#[thrust_macros::requires(dl_wf(*dl) && align.pow2 <= 29 && offset.raw <= 4611686018427387904u64)]
#[thrust_macros::requires(repr_weighs(*repr, r) && niche_ends_by(largest_niche, *dl, offset))]
#[thrust_macros::ensures(forall(|l: Placed, q: USize, q2: USize| !(result == Ok(l) && q == align.pow2 && q2 == l.align.pow2)
    || (l.size.raw < offset.raw + pow2(q) + r && pow2(q2) <= pow2(q) + r)))]
#[thrust_macros::ensures(forall(|q: USize| !(result == Err(LayoutError::SizeOverflow) && q == align.pow2)
    || offset.raw + pow2(q) + r > obj_bound(*dl)))]
#[thrust_macros::ensures(forall(|l: Placed| !(result == Ok(l)) || niche_ends_by(l.largest_niche, *dl, l.size)))]
#[thrust::reveal(repr_weighs)]
fn finish(
    offset: Size,
    mut align: Align,
    repr: &ReprOptions,
    largest_niche: Option<Niche>,
    dl: &TargetDataLayout,
    r: Ghost<Int>,
) -> Result<Placed, LayoutError> {
    if let Some(repr_align) = repr.align {
        align = align.max(repr_align);
    }

    let min_size = offset;
    let size = align_to(min_size, align);
    thrust_macros::proof!(niche_ends_later(&largest_niche, dl, min_size, size));

    if size.bytes() >= obj_size_bound(dl) {
        return Err(LayoutError::SizeOverflow);
    }

    Ok(Placed {
        size,
        align,
        largest_niche,
    })
}

/// The size arithmetic of `univariant_biased` (layout.rs): the prefix, the offset loop over the
/// fields in memory order, the final padding and the object size bound. The memory order is the
/// slice's own order (the bounds hold for every order), and the parts of the loop that do not
/// change the offset (the unsized checks, `max_repr_align`, `offsets[i]`) are left out. The
/// weights `ts`, `p` and `r` are ghosts for the witnesses of layout.rs's `weighs`.
#[thrust_macros::requires(dl_wf(*dl) && fields_wf(fields, *dl))]
#[thrust_macros::requires(weights(fields, ts) && prefix_weighs(kind, *dl, p) && repr_weighs(*repr, r))]
#[thrust_macros::ensures(forall(|l: Placed, s: Int, q: USize| result == Ok(l)
    && weighs(ts, p, r, *dl, s) && q == l.align.pow2 ==> (l.size.raw < s && pow2(q) <= s)))]
#[thrust_macros::ensures(forall(|s: Int| weighs(ts, p, r, *dl, s) && s < obj_bound(*dl)
    ==> result != Err(LayoutError::SizeOverflow)))]
#[thrust_macros::ensures(forall(|l: Placed| result == Ok(l) ==> niche_ends_by(l.largest_niche, *dl, l.size)))]
fn univariant_size(
    fields: &[FieldLayout],
    repr: &ReprOptions,
    kind: StructKind,
    niche_bias: NicheBias,
    dl: &TargetDataLayout,
    ts: Ghost<Seq<Int>>,
    p: Ghost<Int>,
    r: Ghost<Int>,
) -> Result<Placed, LayoutError> {
    let pack = repr.pack;
    let mut align = if pack.is_some() {
        dl.i8_align
    } else {
        dl.aggregate_align
    };
    let mut largest_niche = None;
    let mut largest_niche_available = 0;
    let mut offset = place_prefix(kind, pack, &mut align, dl, p);
    thrust_macros::proof!(no_niche_ends(dl, offset));
    let mut k = 0;
    while k < fields.len() {
        thrust_macros::invariant!(|k: usize, offset: Size, align: Align, largest_niche: Option<Niche>,
            fields: &[FieldLayout], repr: &ReprOptions, dl: &TargetDataLayout, pack: Option<Align>,
            ts: FnParam<Ghost<Seq<Int>>>, p: FnParam<Ghost<Int>>, r: FnParam<Ghost<Int>>|
            dl_wf(*dl) && fields_wf(fields, *dl)
                && weights(fields, ts.at_entry()) && repr_weighs(*repr, r.at_entry())
                && pack == (*repr).pack
                && 0 <= k && k <= (*fields).len()
                && align.pow2 <= 29
                && offset.raw <= 4611686018427387904u64
                && forall(|q: USize, qa: USize, qi: USize| !(q == align.pow2
                    && qa == (*dl).aggregate_align.pow2 && qi == (*dl).i8_align.pow2)
                    || offset.raw + pow2(q) <= p.at_entry() + pow2(qa) + pow2(qi) + sum_first(ts.at_entry(), k))
                && niche_ends_by(largest_niche, *dl, offset));
        thrust_macros::proof!(weight_step(fields, ts, k));
        thrust_macros::proof!(field_at(fields, dl, k));
        place_field(
            &mut offset,
            &mut align,
            &mut largest_niche,
            &mut largest_niche_available,
            &fields[k],
            pack,
            niche_bias,
            dl,
        )?;
        k += 1;
    }

    finish(offset, align, repr, largest_niche, dl, r)
}

fn main() {}
