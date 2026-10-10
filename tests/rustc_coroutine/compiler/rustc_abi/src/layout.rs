use crate::thrust_models;
use std::cmp;
use std::ops::Deref;

use thrust_models::model::Seq;
use thrust_models::{exists, forall};

use crate::rustc_abi::{
    AbiAlign, Align, BackendRepr, FieldsShape, HasDataLayout, LayoutData, Niche, Primitive,
    ReprOptions, Size, StructKind, TargetDataLayout, Variants,
};
use crate::rustc_hashes::Hash64;
use crate::rustc_index::{Idx, IndexSlice, IndexVec};
use crate::case_study::USize;
use crate::case_study::iter::{Filter, Map, collect_index_vec, iter_all};
use crate::case_study::unwrap::Unwrap;

mod coroutine;
mod simple;

enum NicheBias {
    Start,
    End,
}

impl thrust_models::Model for NicheBias {
    type Ty = Self;
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

// The layout an `F` dereferences to, for a contract to name: `layout_is(f, l)` says `**f` is `l`.
// Rewrite (rewrites.md S10): `F`'s bound `Deref<Target = &'a LayoutData<..>>` becomes this trait,
// which has it as a supertrait (probes/layout_ref_niche.rs).
#[thrust_macros::context]
pub trait LayoutRef<'a, FieldIdx: Idx, VariantIdx: Idx>:
    Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model
{
    #[thrust_macros::predicate]
    fn layout_is(self, l: LayoutData<FieldIdx, VariantIdx>) -> bool;
}

#[derive(Clone, Copy /*Debug*/)]
pub struct LayoutCalculator<Cx> {
    pub cx: Cx,
}

/// `2^q`, the bytes of `Align { pow2: q }`.
#[thrust_macros::logic]
#[thrust_macros::variant(q)]
fn pow2(q: u64) -> u64 {
    if q <= 0 { 1 } else { pow2(q - 1) * 2 }
}

/// The sum of the first `k` entries of `ts`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn sum_first(ts: &[u64], k: usize) -> u64 {
    if k <= 0 { 0 } else { sum_first(ts, k - 1) + ts[k - 1] }
}

// Stage 6 spec (README.md, "stage 6"). The `requires` of both methods is the panic condition of
// `univariant_biased` apart from the size: `fields.indices()` builds every field index up to
// `fields.len()`, the single variant is `VariantIdx::new(0)`, and `MaybeUnsized` takes
// `fields.len() - 1`, which wraps below zero (overflow checks are off) so that the slice `[..end]`
// panics; `dl_wf` of the data layout `self.cx` names (the default pointer size is 2, 4 or 8
// bytes, which `Size::checked_add` needs), named by `Cx::dl_of(*self, dl)` since the calculator's
// model is `self.cx`'s; `niche_wf` of every field's largest niche under that layout
// (`Niche::wf_in`, which `Niche::available` and `Primitive::size` need), the field's layout named
// by `LayoutRef::layout_is`; and every field's niche within the field, which rustc's layouts
// satisfy and the sort key's subtractions and the niche of the result rely on.
//
// `univariant_biased` ensures, besides `arbitrary_of`: it fails only with `UnexpectedUnsized`,
// exactly when an unsized field is not the tail of a `MaybeUnsized` struct, which does not depend
// on the order, or with `SizeOverflow`, never when the fields fit in any order
// (`fits_in_any_order`); with `Start` a niche comes from some field's, and with `End` any field's
// niche gives one; the niche is well formed and lies within the size. `univariant` needs these
// for its two `unwrap_without_debug`s on the `End` layout, and requires that the fields fit in any
// order: rustc assumes the `End` layout succeeds whenever the `Start` one does
// (`expect("alt layout should always work")`), but the two orders pad differently, so one of them
// can overflow `checked_add` or `obj_size_bound` alone; summing every field's size and twice its
// alignment, with the prefix, the aggregate and `repr` alignments, bounds the size of every order.
#[thrust_macros::context]
impl<Cx: HasDataLayout> LayoutCalculator<Cx> {
    /// The panic condition of `univariant` and `univariant_biased` apart from the size.
    #[thrust_macros::predicate]
    pub(crate) fn layout_pre<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx,
        F: LayoutRef<'a, FieldIdx, VariantIdx> + thrust_models::Model<Ty: PartialEq>,
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
            && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, n: Niche|
                !(Cx::dl_of(self, dl)
                    && 0 <= i
                    && i < (*fields).len()
                    && F::layout_is((*fields)[i], l)
                    && l.largest_niche == Some(n))
                    || Niche::wf_in(n, dl))
            && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, n: Niche, s: Size|
                !(Cx::dl_of(self, dl)
                    && 0 <= i
                    && i < (*fields).len()
                    && F::layout_is((*fields)[i], l)
                    && l.largest_niche == Some(n)
                    && Primitive::size_in(n.value, dl, s))
                    || n.offset.raw + s.raw <= l.size.raw)
    }

    /// Every order of the fields stays below the object size bound of the data layout.
    #[thrust_macros::predicate]
    pub(crate) fn fits_in_any_order<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx,
        F: LayoutRef<'a, FieldIdx, VariantIdx> + thrust_models::Model<Ty: PartialEq>,
    >(
        self,
        fields: &IndexSlice<FieldIdx, F>,
        repr: &ReprOptions,
        kind: StructKind,
    ) -> bool {
        forall(|dl: TargetDataLayout| !Cx::dl_of(self, dl)
            || exists(|ts: Seq<USize>, b: USize, p: USize, r: USize, qa: USize, qi: USize|
                ts.len() == (*fields).len()
                    && forall(|i: USize, l: LayoutData<FieldIdx, VariantIdx>, q: USize|
                        !(0 <= i && i < ts.len() && F::layout_is((*fields)[i], l) && q == l.align.abi.pow2)
                            || ts[i] == pow2(q) * 2 + l.size.raw)
                    && ((dl.default_address_space_pointer_spec.pointer_size.raw == 2 && b == 32768u64)
                        || (dl.default_address_space_pointer_spec.pointer_size.raw == 4 && b == 2147483648u64)
                        || (dl.default_address_space_pointer_spec.pointer_size.raw == 8 && b == 2305843009213693952u64))
                    && ((forall(|ps: Size, pa: Align| kind != StructKind::Prefixed(ps, pa)) && p == 0)
                        || exists(|ps: Size, pa: Align, q: USize|
                            kind == StructKind::Prefixed(ps, pa) && q == pa.pow2 && p == pow2(q) * 2 + ps.raw))
                    && (((*repr).align == None && r == 0)
                        || exists(|ra: Align, q: USize| (*repr).align == Some(ra) && q == ra.pow2 && r == pow2(q)))
                    && qa == dl.aggregate_align.pow2
                    && qi == dl.i8_align.pow2
                    && sum_first(&ts, ts.len()) + p + r + pow2(qa) + pow2(qi) < b))
    }

    /// An unsized field is not the tail of a `MaybeUnsized` struct.
    #[thrust_macros::predicate]
    fn unsized_misplaced<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx,
        F: LayoutRef<'a, FieldIdx, VariantIdx> + thrust_models::Model<Ty: PartialEq>,
    >(
        fields: &IndexSlice<FieldIdx, F>,
        kind: StructKind,
    ) -> bool {
        exists(|i: USize, l: LayoutData<FieldIdx, VariantIdx>|
            0 <= i && i < (*fields).len()
                && F::layout_is((*fields)[i], l)
                && l.backend_repr == BackendRepr::Memory { sized: false }
                && (!matches!(kind, StructKind::MaybeUnsized) || i + 1 < (*fields).len()))
    }

    /// Some field has a largest niche.
    #[thrust_macros::predicate]
    fn some_field_niche<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx,
        F: LayoutRef<'a, FieldIdx, VariantIdx> + thrust_models::Model<Ty: PartialEq>,
    >(
        fields: &IndexSlice<FieldIdx, F>,
    ) -> bool {
        exists(|i: USize, l: LayoutData<FieldIdx, VariantIdx>, n: Niche|
            0 <= i && i < (*fields).len() && F::layout_is((*fields)[i], l) && l.largest_niche == Some(n))
    }

    #[thrust_macros::requires(Self::layout_pre::<FieldIdx, VariantIdx, F>(*self, fields, kind))]
    #[thrust_macros::requires(Self::fits_in_any_order::<FieldIdx, VariantIdx, F>(*self, fields, repr, kind))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>|
        result != Ok(l) || FieldsShape::<FieldIdx>::arbitrary_of(l.fields, (*fields).len())))]
    pub fn univariant<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx,
        F: LayoutRef<'a, FieldIdx, VariantIdx> + thrust_models::Model<Ty: PartialEq>,
    >(
        &self,
        fields: &IndexSlice<FieldIdx, F>,
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

    #[thrust_macros::requires(Self::layout_pre::<FieldIdx, VariantIdx, F>(*self, fields, kind))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>|
        result != Ok(l) || FieldsShape::<FieldIdx>::arbitrary_of(l.fields, (*fields).len())))]
    #[thrust_macros::ensures(forall(|e: LayoutCalculatorError<<F as thrust_models::Model>::Ty>|
        result != Err(e)
            || e == LayoutCalculatorError::SizeOverflow
            || exists(|f: <F as thrust_models::Model>::Ty| e == LayoutCalculatorError::UnexpectedUnsized(f))))]
    #[thrust_macros::ensures(
        (exists(|f: <F as thrust_models::Model>::Ty| result == Err(LayoutCalculatorError::UnexpectedUnsized(f)))
            ==> Self::unsized_misplaced::<FieldIdx, VariantIdx, F>(fields, kind))
        && (Self::unsized_misplaced::<FieldIdx, VariantIdx, F>(fields, kind)
            ==> exists(|f: <F as thrust_models::Model>::Ty| result == Err(LayoutCalculatorError::UnexpectedUnsized(f)))))]
    #[thrust_macros::ensures(
        Self::fits_in_any_order::<FieldIdx, VariantIdx, F>(*self, fields, repr, kind) ==> result != Err(LayoutCalculatorError::SizeOverflow))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>| result != Ok(l)
        || ((matches!(niche_bias, NicheBias::Start) && l.largest_niche != None) ==> Self::some_field_niche::<FieldIdx, VariantIdx, F>(fields))
            && ((matches!(niche_bias, NicheBias::End) && Self::some_field_niche::<FieldIdx, VariantIdx, F>(fields)) ==> l.largest_niche != None)))]
    #[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>, n: Niche, dl: TargetDataLayout, s: Size|
        !(result == Ok(l) && l.largest_niche == Some(n) && Cx::dl_of(*self, dl))
            || (Niche::wf_in(n, dl) && (!Primitive::size_in(n.value, dl, s) || n.offset.raw + s.raw <= l.size.raw))))]
    fn univariant_biased<
        'a,
        FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
        VariantIdx: Idx,
        F: LayoutRef<'a, FieldIdx, VariantIdx> + thrust_models::Model<Ty: PartialEq>,
    >(
        &self,
        fields: &IndexSlice<FieldIdx, F>,
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
        // Rewrite (rewrites.md R8): `collect_index_vec` for `collect`.
        let mut in_memory_order: IndexVec<u32, FieldIdx> = collect_index_vec(fields.indices());
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
                let max_field_align =
                    Map::new(fields_excluding_tail.iter(), |f: &F| f.align.bytes())
                        .max()
                        .unwrap_or(1);
                // Rewrite (rewrites.md R8): `Map::new` of the niche's `available`, 0 without one,
                // for `filter_map` of the niche and `map` of `available`: the two maxima agree,
                // as `available` is never negative.
                let largest_niche_size = Map::new(fields_excluding_tail.iter(), |f: &F| {
                    f.largest_niche.map_or(0, |n| n.available(dl))
                })
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
            // Rewrite (rewrites.md R8): `Filter::new(it, p)` for `it.filter(p)`.
            let mut non_zst_fields = Filter::new(fields.iter_enumerated(), |&(_, f)| !f.is_zst());

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
        // Rewrite (rewrites.md R8): `!iter_all(it, |f| !p(f))` for `it.any(p)`.
        let uninhabited = !iter_all(fields.iter(), |f| !f.is_uninhabited());

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
