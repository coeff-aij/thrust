//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1

use std::cmp;

use thrust_models::model::UInt;
use thrust_models::{forall, Model};

type USize = UInt;

// `univariant_biased`'s field reordering over a generic `FieldIdx`: the memory order starts as
// the identity (rustc's `collect_index_vec(fields.indices())`), its first `end` entries are sorted
// by one of the two keys of layout.rs, and the result is a permutation of `0..n` as
// `FieldsShape::arbitrary_of` states it, whose inverse `layout()` takes (`memory_index`). The key
// closures read the field an entry names through the `fields` they capture; their written
// contracts (`closure!`) require that field in bounds and, for the `End` key's subtractions, its
// niche within it, and `alignment_group_key` requires nothing. The parameters are typed
// (`|x: &FieldIdx|` for rustc's `|&x|`): `closure!` takes typed parameters, and a contract cannot
// bind a reference pattern. `Idx` is the case study's, without `index_logic`.
#[thrust_macros::context]
trait Idx: Copy + Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::predicate]
    fn can_new(idx: USize) -> bool;

    #[thrust_macros::predicate]
    fn index_is(self, i: USize) -> bool;

    #[thrust_macros::requires(Self::can_new(idx))]
    #[thrust_macros::ensures(Self::index_is(result, idx))]
    fn new(idx: usize) -> Self;

    #[thrust_macros::ensures(Self::index_is(self, result))]
    fn index(self) -> usize;
}

#[thrust_macros::context]
impl Idx for u32 {
    #[thrust_macros::predicate]
    fn can_new(idx: USize) -> bool {
        idx <= 4294967295usize
    }

    #[thrust_macros::predicate]
    fn index_is(self, i: USize) -> bool {
        i == self
    }

    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }

    fn index(self) -> usize {
        self as usize
    }
}

// A field's layout, reduced to what the sort keys read: `available` stands for
// `Niche::available(dl)` and `size` for `n.value.size(dl).bytes()`.
#[derive(Clone, Copy, PartialEq)]
struct Niche {
    offset: u64,
    size: u64,
    available: u64,
}

impl Model for Niche {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq)]
struct FieldLayout {
    size: u64,
    align: u64,
    largest_niche: Option<Niche>,
}

impl Model for FieldLayout {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq)]
enum StructKind {
    AlwaysSized,
    MaybeUnsized,
    Prefixed(u64, u64),
}

impl Model for StructKind {
    type Ty = Self;
}

#[derive(Clone, Copy, PartialEq)]
enum NicheBias {
    Start,
    End,
}

impl Model for NicheBias {
    type Ty = Self;
}

// The pass twin without the fields' niches within the fields: the `End` key's requires, which
// `sort_by_key` asks at the states the closure reaches from the one passed, does not hold.
#[thrust_macros::context]
#[thrust_macros::requires(
    in_memory_order.len() == (*fields).len()
        && (kind != StructKind::MaybeUnsized || (*fields).len() > 0)
        && forall(|k: USize, i: USize|
            !(0 <= k && k < in_memory_order.len() && FieldIdx::index_is(in_memory_order[k], i)) || i == k)
)]
#[thrust_macros::ensures(
    result.len() == (*fields).len()
        && forall(|k: USize, i: USize|
            !(0 <= k && k < result.len() && FieldIdx::index_is(result[k], i)) || (0 <= i && i < result.len()))
        && forall(|k: USize, k2: USize, i: USize|
            !(0 <= k && k < result.len() && 0 <= k2 && k2 < result.len() && !(k == k2)
                && FieldIdx::index_is(result[k], i))
                || !FieldIdx::index_is(result[k2], i))
)]
fn memory_order<FieldIdx: Idx + Model<Ty: PartialEq>>(
    fields: &Vec<FieldLayout>,
    mut in_memory_order: Vec<FieldIdx>,
    kind: StructKind,
    niche_bias: NicheBias,
    pack: Option<u64>,
    optimize_field_order: bool,
    max_field_align: u64,
    largest_niche_size: u64,
) -> Vec<FieldIdx>
where
    <FieldIdx as Model>::Ty: Model<Ty = <FieldIdx as Model>::Ty>,
{
    let end = if let StructKind::MaybeUnsized = kind {
        fields.len() - 1
    } else {
        fields.len()
    };
    let optimizing = &mut in_memory_order[..end];

    if optimize_field_order && fields.len() > 1 {
        let alignment_group_key = thrust_macros::closure!(
            requires(true),
            |layout: &FieldLayout| {
                if let Some(pack) = pack {
                    layout.align.min(pack)
                } else {
                    let align = layout.align;
                    let size = layout.size;
                    let niche_size = layout.largest_niche.map(|n| n.available).unwrap_or(0);

                    let size_as_align = align.max(size).trailing_zeros();
                    let size_as_align = if largest_niche_size > 0 {
                        match niche_bias {
                            NicheBias::Start => max_field_align.trailing_zeros().min(size_as_align),

                            NicheBias::End if niche_size == largest_niche_size => align.trailing_zeros(),
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
                optimizing.sort_by_key(thrust_macros::closure!(
                    captures(fields: &mut &Vec<FieldLayout>),
                    requires(forall(|i: USize| !FieldIdx::index_is(*x, i) || i < (**fields).len())),
                    requires(forall(|i: USize, n: Niche|
                        !(FieldIdx::index_is(*x, i) && (**fields)[i].largest_niche == Some(n))
                            || n.offset + n.size <= (**fields)[i].size)),
                    |x: &FieldIdx| {
                        let f = &fields[x.index()];
                        let field_size = f.size;
                        let niche_size = f.largest_niche.map_or(0, |n| n.available);
                        let niche_size_key = match niche_bias {
                            NicheBias::Start => !niche_size,

                            NicheBias::End => niche_size,
                        };
                        let inner_niche_offset_key = match niche_bias {
                            NicheBias::Start => f.largest_niche.map_or(0, |n| n.offset),
                            NicheBias::End => f.largest_niche.map_or(0, |n| !(field_size - n.size - n.offset)),
                        };

                        (
                            cmp::Reverse(alignment_group_key(f)),
                            niche_size_key,
                            inner_niche_offset_key,
                        )
                    },
                ));
            }

            StructKind::Prefixed(..) => {
                optimizing.sort_by_key(thrust_macros::closure!(
                    captures(fields: &mut &Vec<FieldLayout>),
                    requires(forall(|i: USize| !FieldIdx::index_is(*x, i) || i < (**fields).len())),
                    |x: &FieldIdx| {
                        let f = &fields[x.index()];
                        let niche_size = f.largest_niche.map_or(0, |n| n.available);
                        (alignment_group_key(f), niche_size)
                    },
                ));
            }
        }
    }
    in_memory_order
}

// `IndexSlice::invert_bijective_mapping` with its contract, which the case study proves of
// rustc's body.
#[thrust::trusted]
#[thrust_macros::context]
#[thrust_macros::requires(forall(|k: USize| !(0 <= k && k <= (*order).len()) || I::can_new(k)))]
#[thrust_macros::requires(forall(|k: USize, i: USize|
    !(0 <= k && k < (*order).len() && J::index_is((*order)[k], i)) || i < (*order).len()))]
#[thrust_macros::ensures(result.len() == (*order).len())]
#[thrust_macros::ensures(forall(|k: USize, i: USize|
    !(0 <= k && k < result.len() && I::index_is(result[k], i)) || i < result.len()))]
fn invert_bijective_mapping<I: Idx, J: Idx>(order: &Vec<J>) -> Vec<I>
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <J as Model>::Ty: Model<Ty = <J as Model>::Ty>,
{
    unimplemented!()
}

// The memory index `layout()` takes of the order: one entry per field, each below the number of
// fields.
#[thrust_macros::context]
#[thrust_macros::requires(
    in_memory_order.len() == (*fields).len()
        && (*fields).len() <= 4294967295usize
        && (kind != StructKind::MaybeUnsized || (*fields).len() > 0)
        && forall(|k: USize, i: USize|
            !(0 <= k && k < in_memory_order.len() && FieldIdx::index_is(in_memory_order[k], i)) || i == k)
        && forall(|i: USize, n: Niche|
            !(0 <= i && i < (*fields).len() && (*fields)[i].largest_niche == Some(n))
                || n.offset + n.size <= (*fields)[i].size)
)]
#[thrust_macros::ensures(
    result.len() == (*fields).len()
        && forall(|k: USize| !(0 <= k && k < result.len()) || result[k] < result.len())
)]
fn memory_index<FieldIdx: Idx + Model<Ty: PartialEq>>(
    fields: &Vec<FieldLayout>,
    in_memory_order: Vec<FieldIdx>,
    kind: StructKind,
    niche_bias: NicheBias,
    pack: Option<u64>,
    max_field_align: u64,
    largest_niche_size: u64,
) -> Vec<u32>
where
    <FieldIdx as Model>::Ty: Model<Ty = <FieldIdx as Model>::Ty>,
{
    let order = memory_order(
        fields,
        in_memory_order,
        kind,
        niche_bias,
        pack,
        true,
        max_field_align,
        largest_niche_size,
    );
    invert_bijective_mapping::<u32, FieldIdx>(&order)
}

fn main() {}
