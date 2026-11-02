use crate::thrust_models;
use thrust_models::{exists, forall};

use crate::rustc_abi::layout::{LayoutCalculator, LayoutCalculatorResult, pow2};
use crate::rustc_abi::{
    BackendRepr, FieldsShape, HasDataLayout, Integer, LayoutData, Niche, Primitive, ReprOptions,
    Scalar, Size, StructKind, TagEncoding, TargetDataLayout, VariantLayout, Variants, WrappingRange,
};
use crate::rustc_index::bit_set::{ones, BitIter, BitMatrix, DenseBitSet};
use crate::rustc_index::{Idx, IdxRange, IndexSlice, IndexVec, IterEnumerated, SliceIter};
use crate::case_study::USize;
use crate::case_study::{counts, lemmas};
use crate::case_study::iter::{Filter, Map, collect_index_vec, collect_index_vec_result, iter_all};
use std::iter::{self, Enumerate};
use std::slice::IterMut;

#[derive(Clone, /*Debug,*/ PartialEq)]
enum SavedLocalEligibility<VariantIdx, FieldIdx> {
    Unassigned,
    Assigned(VariantIdx),
    Ineligible(Option<FieldIdx>),
}

impl<VariantIdx: thrust_models::Model, FieldIdx: thrust_models::Model> thrust_models::Model
    for SavedLocalEligibility<VariantIdx, FieldIdx>
{
    type Ty = SavedLocalEligibility<<VariantIdx as thrust_models::Model>::Ty, <FieldIdx as thrust_models::Model>::Ty>;
}

/// The members of the ineligible set below `k` are `Ineligible` (stage 5's property 4), so they
/// and the locals Assigned to any one variant are at most `k`: the count of `layout()`'s
/// per-variant closure (stage 7), at every variant. The `counts.rs` root checks it.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|l: usize| 0 <= l && l < k
    ==> (exists(|li: USize| li == l && DenseBitSet::<LocalIdx>::mem(*s, li))
        ==> exists(|x: Option<<FieldIdx as thrust_models::Model>::Ty>| (*a)[l] == SavedLocalEligibility::Ineligible(x)))))]
#[thrust_macros::ensures(forall(|v: <VariantIdx as thrust_models::Model>::Ty|
    ones((*s).1, k)
        + counts::class_cnt::<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(*a, k, SavedLocalEligibility::Assigned(v))
        <= k))]
fn ones_assigned_disjoint<LocalIdx: Idx + thrust_models::Model, VariantIdx: thrust_models::Model, FieldIdx: thrust_models::Model>(
    s: &DenseBitSet<LocalIdx>,
    a: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    k: usize,
) {
    if k > 0 {
        ones_assigned_disjoint(s, a, k - 1);
        ones_step(s, k - 1);
    } else {
        ones_step(s, k);
    }
}

/// One more bit adds the bit at `k`: `mem` and the step of `ones` read the same bit. With the
/// base case, all `ones_assigned_disjoint` reads of the bit arithmetic.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|z: USize| z == 0 ==> ones((*s).1, z) == 0))]
#[thrust_macros::ensures(
    (DenseBitSet::<LocalIdx>::mem(*s, k) && ones((*s).1, k + 1) == ones((*s).1, k) + 1)
        || (!DenseBitSet::<LocalIdx>::mem(*s, k) && ones((*s).1, k + 1) == ones((*s).1, k)))]
#[thrust::reveal(crate::rustc_index::bit_set::ones, crate::rustc_index::bit_set::DenseBitSet::mem)]
fn ones_step<LocalIdx: Idx + thrust_models::Model>(s: &DenseBitSet<LocalIdx>, k: usize) {}

/// The set's count is the number of its bits below its domain size.
#[thrust_macros::lemma]
#[thrust_macros::ensures(DenseBitSet::<LocalIdx>::card(*s) == ones((*s).1, (*s).0))]
#[thrust::reveal(crate::rustc_index::bit_set::DenseBitSet::card)]
fn card_ones<LocalIdx: Idx + thrust_models::Model>(s: &DenseBitSet<LocalIdx>) {}

// The specification of stage 5 (README.md of the stage files).
//
// Notation below follows the README: `a = result.1` (the `assignments`
// vector) and `inel = result.0` (the `ineligible_locals` set).
//
// The numbered `ensures` clauses are the README's four bullets, 2b the second half of the second.
// Quantifiers in `requires`/`ensures` use `usize`, not `Int`: unlike a
// `predicate` body (see `DenseBitSet::mem` etc., which get special HIR-level
// field-projection handling per `analyze::local_def::predicate_definition`, as
// in values.rs's `dl_wf`), a `requires`/`ensures` body is compiled as an
// ordinary function (`thrust-macros/src/spec.rs`'s `requires_fn`/`ensures_fn`)
// and needs valid Rust: real `.len()` / real `[usize]` indexing.
// `IndexVec` and `IndexSlice` share one model, the slice's `Seq`, so element
// access below reads `[..]` and the length `.len()`.
// An element is then `<LocalIdx as Model>::Ty`, not a real `LocalIdx`, so
// `Idx::index()` is not callable on it (and would not translate in a formula
// anyway): the `Idx::index_is` predicate carries the same fact, with an
// `exists(|i: Int| i == l && ..)` bridge where the position is a `usize`.
//
// The loop invariants replace inference, so each restates what the code after
// it needs: the lengths, the requirements on the arguments, and properties 1,
// 2 and 4 in the form that holds at that loop (`nb_locals` and, once dead,
// `variant_fields` are read at entry through `FnParam`). Where the live
// `variant_fields` and `storage_conflicts` are needed too, a second
// `invariant!` at the same header states the facts about them; the variants
// loops tie the two `variant_fields` together through `variants.0`.
#[thrust_macros::requires(
    forall(|v: usize, f: usize|
        0 <= v && v < (*variant_fields).len()
            && 0 <= f && f < (*variant_fields)[v].len() ==> forall(|i: USize|
            <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i) ==> i < nb_locals))
    // `count(local_b)` takes a column index as a row, so every set bit's column must be below
    // the number of rows: the panic condition, through the matrix's ghost column bound.
    && (*storage_conflicts).num_rows <= nb_locals
    && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
    && BitMatrix::<LocalIdx, LocalIdx>::cols_below(*storage_conflicts, *(*storage_conflicts).col_bound)
    && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
    && forall(|k: USize| 0 <= k && k < nb_locals ==> LocalIdx::can_new(k))
    && forall(|n: USize| 0 <= n && n <= nb_locals ==> FieldIdx::can_new(n))
    && forall(|v: USize| 0 <= v && v <= (*variant_fields).len() ==> VariantIdx::can_new(v))
)]
#[thrust_macros::ensures(
    // `assignments` has one entry per local, and `inel` is a set over the locals, so its
    // iterator yields locals below `nb_locals`.
    result.1.len() == nb_locals
    && result.0.0 == nb_locals
    // 1. Unassigned locals never appear in any variant's field list.
    && forall(|l: usize| 0 <= l && l < nb_locals && result.1[l] == SavedLocalEligibility::Unassigned ==> forall(|v: usize, f: usize|
            0 <= v && v < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[v].len() ==> !thrust_models::exists(|i: USize|
                i == l
                    && <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i))))
    // 2. An Assigned(v) local appears in variant v's field list.
    && forall(|l: usize, v: usize|
        0 <= l && l < nb_locals
            && thrust_models::exists(|vi: <VariantIdx as thrust_models::Model>::Ty|
                thrust_models::exists(|vn: USize| vn == v && <VariantIdx as Idx>::index_is(vi, vn))
                    && result.1[l] == SavedLocalEligibility::Assigned(vi)) ==> (v < (*variant_fields).len()
            && thrust_models::exists(|f: usize|
                0 <= f && f < (*variant_fields)[v].len()
                    && thrust_models::exists(|i: USize|
                        i == l
                            && <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i)))))
    // 2b. A local a variant lists is Assigned to that variant if it is Assigned at all, which
    // `layout()`'s `Assigned(_) => unreachable!()` needs.
    && forall(|l: usize, w: usize, f: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
        0 <= l && l < nb_locals
            && 0 <= w && w < (*variant_fields).len()
            && 0 <= f && f < (*variant_fields)[w].len()
            && thrust_models::exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][f], i))
            && result.1[l] == SavedLocalEligibility::Assigned(vi) ==> forall(|vn: USize| <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w))
    // 2c. An Assigned local appears at most once in a variant's field list: rustc's pass makes a
    // local it sees a second time ineligible. `layout()` counts a variant's Assigned locals by it.
    && forall(|l: usize, w: usize, f: usize, g: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
        0 <= l && l < nb_locals
            && 0 <= w && w < (*variant_fields).len()
            && 0 <= f && f < (*variant_fields)[w].len()
            && 0 <= g && g < (*variant_fields)[w].len()
            && thrust_models::exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][f], i))
            && thrust_models::exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][g], i))
            && result.1[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
    // 3. An ineligible local has its promoted field index, below the number of members of
    // `inel` (`DenseBitSet::card`, the position in `inel.iter()`'s enumeration).
    && forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
        0 <= l && l < nb_locals && result.1[l] == SavedLocalEligibility::Ineligible(x) ==> thrust_models::exists(|k: <FieldIdx as thrust_models::Model>::Ty|
            x == Some(k) && forall(|i: USize| <FieldIdx as Idx>::index_is(k, i) ==> i < DenseBitSet::<LocalIdx>::card(result.0))))
    // 4. Membership in `inel` matches being `Ineligible(_)`, written as an `<==>` via two `==>`.
    // `mem` takes an `Int` (its declared `usize` parameter is lowered to
    // `Int` by `#[thrust_macros::predicate]`, see the note above the
    // `requires`), but real `Vec` indexing needs a literal `usize`; the
    // `exists(|li: Int| li == l && ..)` below is a `usize -> Int` bridge
    // (`Int: PartialEq<T> where T: Model<Ty = Int>`, and `usize` is one).
    && forall(|l: usize| 0 <= l && l < nb_locals ==> (thrust_models::exists(|li: USize| li == l && DenseBitSet::<LocalIdx>::mem(result.0, li)) ==> thrust_models::exists(|x: Option<<FieldIdx as thrust_models::Model>::Ty>| result.1[l] == SavedLocalEligibility::Ineligible(x))))
    && forall(|l: usize| 0 <= l && l < nb_locals ==> (thrust_models::exists(|x: Option<<FieldIdx as thrust_models::Model>::Ty>| result.1[l] == SavedLocalEligibility::Ineligible(x)) ==> thrust_models::exists(|li: USize| li == l && DenseBitSet::<LocalIdx>::mem(result.0, li))))
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

    // Rewrite (rewrites.md R5): `while let` for `for`, since the inner loop's invariant names this
    // iterator and the iterator of every `for` loop is `iter`.
    let mut variants = variant_fields.iter_enumerated();
    while let Some((variant_index, fields)) = variants.next() {
        // Properties 1 and 2 over the variants before `variants.1`, and 4.
        thrust_macros::invariant!(
            |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, variants: IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>, nb_locals: thrust_models::FnParam<usize>|
            assignments.len() == nb_locals.at_entry()
            && ineligible_locals.0 == nb_locals.at_entry()
            && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
            && 0 <= DenseBitSet::<LocalIdx>::card(ineligible_locals)
            && DenseBitSet::<LocalIdx>::card(ineligible_locals) <= ineligible_locals.0
            && variants.1 >= 0 && variants.1 <= variants.0.len() && *variants.0 == *variant_fields
            && forall(|v: USize| 0 <= v && v <= (*variant_fields).len() ==> <VariantIdx as Idx>::can_new(v))
            && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> i < (*variant_fields).len())
            && (*storage_conflicts).num_rows <= nb_locals.at_entry()
            && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
            && BitMatrix::<LocalIdx, LocalIdx>::cols_below(*storage_conflicts, *(*storage_conflicts).col_bound)
            && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
            && forall(|k: USize| 0 <= k && k < nb_locals.at_entry() ==> <LocalIdx as Idx>::can_new(k))
            && forall(|n: USize| 0 <= n && n <= nb_locals.at_entry() ==> <FieldIdx as Idx>::can_new(n))
            && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x) ==> (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
            && forall(|l: USize| 0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) ==> assignments[l] == SavedLocalEligibility::Ineligible(None))
        );
        thrust_macros::invariant!(
            |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variants: IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
            *variants.0 == *variant_fields.at_entry()
            && forall(|v: USize, f: USize| 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> forall(|i: USize| <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], i) ==> i < nb_locals.at_entry()))
            && forall(|l: USize, v: USize, f: USize|
                0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                    && 0 <= v && v < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
            && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> (i < (*variant_fields.at_entry()).len()
                    && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
            && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                0 <= l && l < nb_locals.at_entry() && 0 <= w && w < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                    && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                    && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w)
            && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                0 <= l && l < nb_locals.at_entry() && 0 <= w && w < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                    && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                    && assignments[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
        );
        for local in fields {
            // `variant_index` is the variant at `variants.1 - 1`, whose fields `iter` walks;
            // property 1 covers the variants before it and its locals before `iter.1`.
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, variants: IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, iter: SliceIter<LocalIdx>, variant_index: VariantIdx, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>, nb_locals: thrust_models::FnParam<usize>|
                assignments.len() == nb_locals.at_entry()
                && ineligible_locals.0 == nb_locals.at_entry()
                && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                && 0 <= DenseBitSet::<LocalIdx>::card(ineligible_locals)
                && DenseBitSet::<LocalIdx>::card(ineligible_locals) <= ineligible_locals.0
                && variants.1 >= 0 && variants.1 <= variants.0.len() && *variants.0 == *variant_fields
                && forall(|v: USize| 0 <= v && v <= (*variant_fields).len() ==> <VariantIdx as Idx>::can_new(v))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> i < (*variant_fields).len())
                && (*storage_conflicts).num_rows <= nb_locals.at_entry()
                && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
                && BitMatrix::<LocalIdx, LocalIdx>::cols_below(*storage_conflicts, *(*storage_conflicts).col_bound)
                && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
                && forall(|k: USize| 0 <= k && k < nb_locals.at_entry() ==> <LocalIdx as Idx>::can_new(k))
                && forall(|n: USize| 0 <= n && n <= nb_locals.at_entry() ==> <FieldIdx as Idx>::can_new(n))
                && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x) ==> (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
                && forall(|l: USize| 0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) ==> assignments[l] == SavedLocalEligibility::Ineligible(None))
                && iter.1 >= 0 && iter.1 <= iter.0.len()
                && forall(|k: USize| 0 <= k && k < iter.0.len() ==> forall(|i: USize| <LocalIdx as Idx>::index_is(iter.0[k], i) ==> i < nb_locals.at_entry()))
                && forall(|i: USize| <VariantIdx as Idx>::index_is(variant_index, i) ==> i < (*variant_fields).len())
                && forall(|p: USize| <VariantIdx as Idx>::index_is(variant_index, p) ==> p + 1 == variants.1)
            );
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variants: IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, iter: SliceIter<LocalIdx>, variant_index: VariantIdx, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
                *variants.0 == *variant_fields.at_entry()
                && forall(|v: USize, f: USize| 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> forall(|i: USize| <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], i) ==> i < nb_locals.at_entry()))
                && forall(|p: USize| <VariantIdx as Idx>::index_is(variant_index, p) ==> *iter.0 == (*variant_fields.at_entry())[p])
                && forall(|l: USize, v: USize, f: USize|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v + 1 < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|l: USize, k: USize|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned && 0 <= k && k < iter.1 ==> !<LocalIdx as Idx>::index_is(iter.0[k], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w + 1 < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w + 1 < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
                && forall(|l: USize, k: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    0 <= l && l < nb_locals.at_entry() && 0 <= k && k < iter.1 && <LocalIdx as Idx>::index_is(iter.0[k], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn + 1 == variants.1)
                && forall(|l: USize, j: USize, k: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    0 <= l && l < nb_locals.at_entry() && 0 <= j && j < iter.1 && 0 <= k && k < iter.1
                        && <LocalIdx as Idx>::index_is(iter.0[j], l) && <LocalIdx as Idx>::index_is(iter.0[k], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) ==> j == k)
            );
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

    // Rewrite (rewrites.md R5): `while let` for `for`, since the inner loop's invariant names this
    // iterator and the iterator of every `for` loop is `iter`.
    let mut rows = storage_conflicts.rows();
    while let Some(local_a) = rows.next() {
        // The loop only turns locals into `Ineligible(None)` members of `ineligible_locals`, so
        // properties 1, 2 and 4 carry over.
        thrust_macros::invariant!(
            |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, rows: IdxRange<LocalIdx>, storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, nb_locals: thrust_models::FnParam<usize>|
            assignments.len() == nb_locals.at_entry()
            && ineligible_locals.0 == nb_locals.at_entry()
            && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
            && 0 <= DenseBitSet::<LocalIdx>::card(ineligible_locals)
            && DenseBitSet::<LocalIdx>::card(ineligible_locals) <= ineligible_locals.0
            && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> i < (*variant_fields).len())
            && (*storage_conflicts).num_rows <= nb_locals.at_entry()
            && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
            && BitMatrix::<LocalIdx, LocalIdx>::cols_below(*storage_conflicts, *(*storage_conflicts).col_bound)
            && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
            && forall(|k: USize| 0 <= k && k < nb_locals.at_entry() ==> <LocalIdx as Idx>::can_new(k))
            && forall(|n: USize| 0 <= n && n <= nb_locals.at_entry() ==> <FieldIdx as Idx>::can_new(n))
            && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x) ==> (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
            && forall(|l: USize| 0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) ==> assignments[l] == SavedLocalEligibility::Ineligible(None))
            && rows.start >= 0 && rows.end == (*storage_conflicts).num_rows
        );
        thrust_macros::invariant!(
            |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
            forall(|l: USize, v: USize, f: USize|
                0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                    && 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
            && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> (i < (*variant_fields.at_entry()).len()
                    && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
            && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                    && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                    && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w)
            && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                    && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                    && assignments[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
        );
        let conflicts_a = storage_conflicts.count(local_a);
        if ineligible_locals.contains(local_a) {
            continue;
        }

        for local_b in storage_conflicts.iter(local_a) {
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, iter: BitIter<LocalIdx>, rows: IdxRange<LocalIdx>, local_a: LocalIdx, storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, nb_locals: thrust_models::FnParam<usize>|
                assignments.len() == nb_locals.at_entry()
                && ineligible_locals.0 == nb_locals.at_entry()
                && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                && 0 <= DenseBitSet::<LocalIdx>::card(ineligible_locals)
                && DenseBitSet::<LocalIdx>::card(ineligible_locals) <= ineligible_locals.0
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> i < (*variant_fields).len())
                && (*storage_conflicts).num_rows <= nb_locals.at_entry()
                && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
                && BitMatrix::<LocalIdx, LocalIdx>::cols_below(*storage_conflicts, *(*storage_conflicts).col_bound)
                && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
                && forall(|k: USize| 0 <= k && k < nb_locals.at_entry() ==> <LocalIdx as Idx>::can_new(k))
                && forall(|n: USize| 0 <= n && n <= nb_locals.at_entry() ==> <FieldIdx as Idx>::can_new(n))
                && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x) ==> (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
                && forall(|l: USize| 0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) ==> assignments[l] == SavedLocalEligibility::Ineligible(None))
                && rows.start >= 0 && rows.end == (*storage_conflicts).num_rows
                && forall(|i: USize| <LocalIdx as Idx>::index_is(local_a, i) ==> i < nb_locals.at_entry())
                && iter.4 == *(*storage_conflicts).col_bound
                && 0 <= iter.5 && 0 <= iter.6 && iter.5 + iter.6 <= iter.4
            );
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
                forall(|l: USize, v: USize, f: USize|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
            );
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
        for assignment in &assignments {
            // `used_variants` is the domain of the variants assigned so far; the rest is unchanged.
            thrust_macros::invariant!(
                |used_variants: DenseBitSet<VariantIdx>, iter: SliceIter<SavedLocalEligibility<VariantIdx, FieldIdx>>, assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
                iter.1 >= 0 && iter.1 <= iter.0.len()
                && *iter.0 == assignments
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> i < used_variants.0)
                // `insert` requires it of `used_variants`.
                && DenseBitSet::<VariantIdx>::words_cover_domain(used_variants)
                && assignments.len() == nb_locals.at_entry()
                && ineligible_locals.0 == nb_locals.at_entry()
                && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                && 0 <= DenseBitSet::<LocalIdx>::card(ineligible_locals)
                && DenseBitSet::<LocalIdx>::card(ineligible_locals) <= ineligible_locals.0
                && forall(|k: USize| 0 <= k && k < nb_locals.at_entry() ==> <LocalIdx as Idx>::can_new(k))
                && forall(|n: USize| 0 <= n && n <= nb_locals.at_entry() ==> <FieldIdx as Idx>::can_new(n))
                && forall(|l: USize, v: USize, f: USize|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
                && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x) ==> (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
                && forall(|l: USize| 0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) ==> assignments[l] == SavedLocalEligibility::Ineligible(None))
            );
            if let Assigned(idx) = assignment {
                used_variants.insert(*idx);
            }
        }
        if used_variants.count() < 2 {
            for assignment in assignments.iter_mut() {
                // `assignments` is the final sequence of the borrow, `Ineligible(None)` below the cursor.
                thrust_macros::invariant!(
                    |iter: IterMut<SavedLocalEligibility<VariantIdx, FieldIdx>>, assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, nb_locals: thrust_models::FnParam<usize>|
                    iter.0.len() == nb_locals.at_entry() && iter.1.len() == nb_locals.at_entry()
                    && 0 <= iter.2 && iter.2 <= iter.0.len()
                    && assignments == iter.1
                    && forall(|k: USize| 0 <= k && k < iter.2 ==> iter.1[k] == SavedLocalEligibility::Ineligible(None))
                    && ineligible_locals.0 == nb_locals.at_entry()
                    && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                    && 0 <= DenseBitSet::<LocalIdx>::card(ineligible_locals)
                    && DenseBitSet::<LocalIdx>::card(ineligible_locals) <= ineligible_locals.0
                    && forall(|k: USize| 0 <= k && k < nb_locals.at_entry() ==> <LocalIdx as Idx>::can_new(k))
                    && forall(|n: USize| 0 <= n && n <= nb_locals.at_entry() ==> <FieldIdx as Idx>::can_new(n))
                );
                *assignment = Ineligible(None);
            }
            ineligible_locals.insert_all();
        }
    }

    {
        for (idx, local) in ineligible_locals.iter().enumerate() {
            // A member of `ineligible_locals` is either still to come from the iterator and
            // `Ineligible(None)`, or already `Ineligible(Some(k))` with `k` below the number of
            // members; at the end none is still to come, which gives property 3.
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, iter: Enumerate<BitIter<LocalIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
                assignments.len() == nb_locals.at_entry()
                && ineligible_locals.0 == nb_locals.at_entry()
                && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                && 0 <= DenseBitSet::<LocalIdx>::card(ineligible_locals)
                && DenseBitSet::<LocalIdx>::card(ineligible_locals) <= ineligible_locals.0
                && iter.0.4 == ineligible_locals.0 && iter.1 == iter.0.5
                && 0 <= iter.1 && iter.1 <= iter.0.4
                && 0 <= iter.0.6 && iter.0.5 + iter.0.6 == DenseBitSet::<LocalIdx>::card(ineligible_locals)
                && forall(|k: USize| 0 <= k && k < nb_locals.at_entry() ==> <LocalIdx as Idx>::can_new(k))
                && forall(|n: USize| 0 <= n && n <= nb_locals.at_entry() ==> <FieldIdx as Idx>::can_new(n))
                && forall(|l: USize, v: USize, f: USize|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
                && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x) ==> DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                && forall(|l: USize| iter.0.7[l] != 0 ==> DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                && forall(|l: USize| 0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) ==> (iter.0.7[l] != 0 && assignments[l] == SavedLocalEligibility::Ineligible(None))
                    || exists(|k: <FieldIdx as thrust_models::Model>::Ty| assignments[l] == SavedLocalEligibility::Ineligible(Some(k))
                        && forall(|i: USize| <FieldIdx as Idx>::index_is(k, i) ==> i < DenseBitSet::<LocalIdx>::card(ineligible_locals))))
            );
            assignments[local] = Ineligible(Some(FieldIdx::new(idx)));
        }
    }

    (ineligible_locals, assignments)
}

// Rewrite (rewrites.md R14): the part of `layout()`'s per-variant closure that collects the
// layouts of the variant's fields, as a function whose contract states what the closure reads of
// them: no more than the locals Assigned to the variant (`class_cnt`), each a layout of
// `local_layouts`. Its `requires` is the closure's at the variant's entries: each is a local
// below n that is not `Unassigned` (property 1), Assigned to this variant if at all (property 2b),
// and an Assigned local appears once (property 2c).
#[thrust_macros::requires(
    (*assignments).len() == (*local_layouts).len()
        && forall(|k: USize| 0 <= k && k <= (*variant_fields).len() ==> <FieldIdx as Idx>::can_new(k))
        && forall(|f: usize, i: USize|
            0 <= f && f < (*variant_fields).len() && <LocalIdx as Idx>::index_is((*variant_fields)[f], i)
                ==> i < (*local_layouts).len())
        && forall(|l: usize, f: usize|
            !(0 <= l && l < (*assignments).len()
                && 0 <= f && f < (*variant_fields).len()
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i)))
            || (*assignments)[l] != SavedLocalEligibility::Unassigned)
        && forall(|l: usize, f: usize, vi: <VariantIdx as thrust_models::Model>::Ty, w: USize|
            !(0 <= l && l < (*assignments).len()
                && 0 <= f && f < (*variant_fields).len()
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i))
                && (*assignments)[l] == SavedLocalEligibility::Assigned(vi)
                && <VariantIdx as Idx>::index_is(index, w))
            || forall(|vn: USize| !<VariantIdx as Idx>::index_is(vi, vn) || vn == w))
        && forall(|l: usize, f: usize, g: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
            !(0 <= l && l < (*assignments).len()
                && 0 <= f && f < (*variant_fields).len()
                && 0 <= g && g < (*variant_fields).len()
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i))
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[g], i))
                && (*assignments)[l] == SavedLocalEligibility::Assigned(vi))
            || f == g)
)]
#[thrust_macros::ensures(
    result.len()
        <= counts::class_cnt::<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
            *assignments, (*assignments).len(), SavedLocalEligibility::Assigned(index))
        && forall(|k: USize|
            !(0 <= k && k < result.len())
            || exists(|i: USize| 0 <= i && i < (*local_layouts).len() && result[k] == (*local_layouts)[i]))
)]
#[thrust_macros::context]
fn variant_field_layouts<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    LocalIdx: Idx + thrust_models::Model,
>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    index: VariantIdx,
    local_layouts: &IndexSlice<LocalIdx, F>,
) -> IndexVec<FieldIdx, F> {
    use SavedLocalEligibility::*;

    // Rewrite (rewrites.md R8): the `Filter` is bound to a name, for the lemma below.
    // `Filter` takes a `Fn` closure, whose clauses read a capture as the reference it is
    // (`*assignments`); `Map` takes an `FnMut` one, whose clauses read it through the
    // closure's state (`**local_layouts`). The other form panics (#152).
    let accepted = Filter::new(variant_fields.iter(), thrust_macros::closure!(
            captures(
                assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
                index: &VariantIdx,
            ),
            requires(
                <LocalIdx as Idx>::index_logic(**local) < (*assignments).len()
                    && (*assignments)[<LocalIdx as Idx>::index_logic(**local)] != SavedLocalEligibility::Unassigned
                    && forall(|vi: <VariantIdx as thrust_models::Model>::Ty, w: USize|
                        !((*assignments)[<LocalIdx as Idx>::index_logic(**local)] == SavedLocalEligibility::Assigned(vi)
                            && <VariantIdx as Idx>::index_is(*index, w))
                        || forall(|vn: USize| !<VariantIdx as Idx>::index_is(vi, vn) || vn == w))
            ),
            ensures(result == ((*assignments)[<LocalIdx as Idx>::index_logic(**local)] == SavedLocalEligibility::Assigned(*index))),
            |local: &&LocalIdx| -> bool {
                match assignments[**local] {
                    // Unreachable by eligibility.rs's stage-5 property 1 (an `Unassigned`
                    // local never appears in any variant's field list).
                    Unassigned => unreachable!(),
                    Assigned(v) if v == index => true,
                    // Unreachable by property 2b (a listed local is Assigned to its own
                    // variant) and `Idx::index_is_injective` (`v == index`).
                    Assigned(_) => unreachable!("assignment does not match variant"),
                    Ineligible(_) => false,
                }
            },
        ));
    // The map closure's `requires` at every item the filter yields (`Map::new`'s
    // `next_precondition`): the items are entries of the variant's field list.
    thrust_macros::proof!(counts::filter_yields_below(&accepted, local_layouts.len()));
    let variant_only_tys = Map::new(
        accepted,
        thrust_macros::closure!(
            captures(local_layouts: &mut &IndexSlice<LocalIdx, F>),
            requires(<LocalIdx as Idx>::index_logic(*local) < (**local_layouts).len()),
            ensures(result == (**local_layouts)[<LocalIdx as Idx>::index_logic(*local)]),
            |local: &LocalIdx| -> F { local_layouts[*local] },
        ),
    );

    // The fields collected below are no more than the locals Assigned to the variant: the
    // filter accepts the entries Assigned to it, which name distinct locals (property
    // 2c). With the `requires` on c, the count sites 1 and 3 need.
    thrust_macros::proof!(counts::filter_count(
        &variant_only_tys,
        variant_fields,
        &assignments,
        &Assigned(index),
        variant_fields.len(),
        assignments.len(),
    ));

    // Rewrite (rewrites.md R8): `collect_index_vec` for `collect`.
    collect_index_vec(variant_only_tys)
}

// Rewrite (rewrites.md R12): the part of `layout()`'s per-variant closure that combines the
// variant's offsets and memory order with the promoted ones, as a function whose `requires`
// states what the code reads: the memory order is a permutation of `0..m` with m offsets
// (univariant's `arbitrary_of`), `FieldIdx` and `u32` reach c + m (c the promoted fields), every
// entry of the variant is a local below n that is not `Unassigned` (property 1), and an
// `Ineligible` local's field index is below c (property 3). Its `ensures` is `true`: `layout()`
// states nothing of the variants it returns.
#[thrust_macros::requires(
    offsets.len() == in_memory_order.len()
        && forall(|k: USize| 0 <= k && k <= (*variant_fields).len() ==> <FieldIdx as Idx>::can_new(k))
        && forall(|k: USize| 0 <= k && k <= in_memory_order.len() ==> <u32 as Idx>::can_new(k))
        && forall(|k: USize, i: USize|
            0 <= k && k < in_memory_order.len() && <FieldIdx as Idx>::index_is(in_memory_order[k], i) ==> i < in_memory_order.len())
        && forall(|k: USize| 0 <= k && k <= (*promoted_memory_index).len() + in_memory_order.len() ==> <FieldIdx as Idx>::can_new(k))
        && (*promoted_memory_index).len() + in_memory_order.len() <= 4294967295usize
        && forall(|k: USize, i: USize|
            0 <= k && k < (*promoted_memory_index).len() && <u32 as Idx>::index_is((*promoted_memory_index)[k], i)
                ==> i < (*promoted_memory_index).len())
        && forall(|f: usize, i: USize|
            0 <= f && f < (*variant_fields).len() && <LocalIdx as Idx>::index_is((*variant_fields)[f], i)
                ==> (i < (*assignments).len() && (*assignments)[i] != SavedLocalEligibility::Unassigned))
)]
// Property 3. The fail root layout.rs leaves it out, and the `unwrap` of an `Ineligible` local's
// field index is refuted.
#[cfg_attr(not(thrust_layout_fail), thrust_macros::requires(
    forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
            0 <= l && l < (*assignments).len() && (*assignments)[l] == SavedLocalEligibility::Ineligible(x)
                ==> exists(|k: <FieldIdx as thrust_models::Model>::Ty|
                    x == Some(k)
                        && forall(|i: USize|
                            <FieldIdx as Idx>::index_is(k, i)
                                ==> (i < (*promoted_offsets).len() && i < (*promoted_memory_index).len()))))
))]
#[thrust_macros::ensures(true)]
#[thrust_macros::context]
fn combine_offsets<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
    offsets: IndexVec<FieldIdx, Size>,
    in_memory_order: IndexVec<u32, FieldIdx>,
) -> (IndexVec<FieldIdx, Size>, IndexVec<u32, FieldIdx>) {
    use SavedLocalEligibility::*;

    // `invert_bijective_mapping` needs `u32::can_new` up to the number of fields m, and
    // `FieldIdx::new(invalid_field_idx)` needs `FieldIdx::can_new(c + m)`: c + m <= n by
    // `filter_count` above and the closure's `requires` on c.
    let memory_index = in_memory_order.invert_bijective_mapping();
    let invalid_field_idx = promoted_memory_index.len() + memory_index.len();
    let mut combined_in_memory_order =
        IndexVec::from_elem_n(FieldIdx::new(invalid_field_idx), invalid_field_idx);

    let mut offsets_and_memory_index = iter::zip(offsets, memory_index);
    // Rewrite (rewrites.md R8): `Map::new` and `collect_index_vec` for `map` and `collect`.
    // The closure's contract: its `requires` states what its body reads, of the entry it is given
    // (a local below n that is not `Unassigned`) and of its captures (property 3, the promoted
    // memory index below c, `combined_in_memory_order`'s length c + m, and the zip's `inv`, which
    // `next` requires). Its `hist_inv` keeps
    // what the `requires` reads of the captures across calls: the shared captures are unchanged
    // and the writes to `combined_in_memory_order` keep its length. `Map::new`'s
    // `next_precondition` follows from `combine_offsets`' `requires` on the variant's entries.
    let combined_offsets = collect_index_vec(Map::new(
        variant_fields.iter_enumerated(),
        thrust_macros::closure!(
        captures(
            assignments: &mut &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
            offsets_and_memory_index: &mut &mut std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>>,
            promoted_memory_index: &mut &IndexVec<FieldIdx, u32>,
            invalid_field_idx: &mut &usize,
            promoted_offsets: &mut &IndexVec<FieldIdx, Size>,
            combined_in_memory_order: &mut &mut IndexVec<u32, FieldIdx>,
        ),
        requires(
            <LocalIdx as Idx>::index_logic(*local) < (**assignments).len()
                && (**assignments)[<LocalIdx as Idx>::index_logic(*local)] != SavedLocalEligibility::Unassigned
                && forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    !(0 <= l && l < (**assignments).len() && (**assignments)[l] == SavedLocalEligibility::Ineligible(x))
                    || exists(|k: <FieldIdx as thrust_models::Model>::Ty|
                        x == Some(k)
                            && forall(|i: USize|
                                !<FieldIdx as Idx>::index_is(k, i)
                                    || (i < (**promoted_offsets).len() && i < (**promoted_memory_index).len()))))
                && forall(|k: USize, i: USize|
                    !(0 <= k && k < (**promoted_memory_index).len() && <u32 as Idx>::index_is((**promoted_memory_index)[k], i))
                    || i < (**promoted_memory_index).len())
                && (**promoted_memory_index).len() <= **invalid_field_idx
                && **invalid_field_idx <= 4294967295usize
                && (**combined_in_memory_order).len() == **invalid_field_idx
                && <std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>> as crate::IteratorSpec>::inv(**offsets_and_memory_index)
        ),
        ensures(true),
        hist_inv(
            *assignments == !assignments
                && *promoted_memory_index == !promoted_memory_index
                && *promoted_offsets == !promoted_offsets
                && *invalid_field_idx == !invalid_field_idx
                && (**combined_in_memory_order).len() == (*!combined_in_memory_order).len()
                && (!<std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>> as crate::IteratorSpec>::inv(**offsets_and_memory_index)
                    || <std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>> as crate::IteratorSpec>::inv(*!offsets_and_memory_index))
        ),
        |(i, local): (FieldIdx, &LocalIdx)| -> Size {
            let (offset, memory_index) = match assignments[*local] {
                // Unreachable, as above.
                Unassigned => unreachable!(),
                Assigned(_) => {
                    // Rewrite (rewrites.md R12): the pair, c and c + m are bound to names, for the
                    // `assume!`, which names local variables only (not a closure's captures).
                    let pair = offsets_and_memory_index.next();
                    let promoted_count = promoted_memory_index.len();
                    let bound = invalid_field_idx;
                    // Assumed (not proved): `next` returns a pair, and its memory index j has
                    // c + j < c + m = `invalid_field_idx`. rustc's code makes it true: the zip has
                    // m pairs (univariant's `arbitrary_of`: m offsets, and the inverted order has
                    // m entries); the m fields are the entries the filter accepted, those whose
                    // local is Assigned to this variant, in order; this closure runs once per
                    // entry, in order (`iter_enumerated`), and takes a pair only at those
                    // entries, so it never takes more than m; and every entry of the inverted
                    // order is below m (`invert_bijective_mapping`). With it, the `u32` sum stays
                    // below c + m <= u32::MAX and indexes `combined_in_memory_order`. Not proved:
                    // the proof needs m equal to the count of Assigned entries (`filter_count`
                    // gives m <= it) and a `hist_inv` of this closure tying the pairs left to
                    // the position.
                    thrust_macros::assume!(
                        |pair: Option<(Size, u32)>, promoted_count: usize, bound: usize|
                            exists(|o: Size, j: <u32 as thrust_models::Model>::Ty| pair == Some((o, j)) && promoted_count + j < bound)
                    );
                    // Reachability twin of the `assume!` (fail root layout_reach.rs): the path after it is
                    // reachable, so the `assume!` makes no proof here vacuous.
                    #[cfg(thrust_layout_reach_pair)]
                    thrust_macros::proof_assert!(|| false);
                    let (offset, memory_index) = pair.unwrap();
                    (offset, promoted_memory_index.len() as u32 + memory_index)
                }
                Ineligible(field_idx) => {
                    // `.unwrap()`: `field_idx == Some(_)` by eligibility.rs's stage-5
                    // property 3.
                    let field_idx = field_idx.unwrap();
                    (
                        // `field_idx` is below the set's count c (property 3),
                        // which is `offsets_b.len()` (the prefix length and `split_off`),
                        // and `promoted_memory_index` has at least c entries
                        // (the permutation split).
                        promoted_offsets[field_idx],
                        promoted_memory_index[field_idx],
                    )
                }
            };
            // `combined_in_memory_order[memory_index]`: an Assigned local's index is below
            // `invalid_field_idx` by the `assume!` above, an Ineligible local's is an entry of
            // `promoted_memory_index`, below c (`invert_bijective_mapping`).
            combined_in_memory_order[memory_index] = i;
            offset
        },
        ),
    ));

    combined_in_memory_order
        .raw
        .retain(|&i| i.index() != invalid_field_idx);

    (combined_offsets, combined_in_memory_order)
}

// Rewrite (rewrites.md R11): the loop of `layout()` that splits `in_memory_order` at `b_start`,
// as a function whose contract states what `layout()` reads of the two parts. The order is a
// permutation of `0..n` (univariant's `arbitrary_of`, stated as there), so the counting lemmas
// give the second part exactly n - b entries, each below n - b.
#[thrust_macros::requires(
    in_memory_order.len() == n
        && <FieldIdx as Idx>::index_logic(b_start) <= n
        && forall(|k: USize| 0 <= k && k <= n ==> <FieldIdx as Idx>::can_new(k))
        && forall(|k: USize, i: USize|
            0 <= k && k < n && <FieldIdx as Idx>::index_is(in_memory_order[k], i) ==> i < n)
        && forall(|k: USize, k2: USize, i: USize|
            0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2) && <FieldIdx as Idx>::index_is(in_memory_order[k], i)
                ==> !<FieldIdx as Idx>::index_is(in_memory_order[k2], i))
)]
#[thrust_macros::ensures(
    result.1.len() == n - <FieldIdx as Idx>::index_logic(b_start)
        && forall(|k: USize, i: USize|
            0 <= k && k < result.1.len() && <FieldIdx as Idx>::index_is(result.1[k], i) ==> i < result.1.len())
)]
#[thrust_macros::context]
fn split_in_memory_order<FieldIdx: Idx + thrust_models::Model>(
    in_memory_order: IndexVec<u32, FieldIdx>,
    b_start: FieldIdx,
    n: usize,
) -> (IndexVec<u32, FieldIdx>, IndexVec<u32, FieldIdx>) {
    // The loop is rustc's. Its invariant is that of probes/permutation_split.rs, which verifies
    // the same loop over a `Vec`: the bounds of the `requires`, carried for `FieldIdx::new`, and
    // the count of the split.
    let order = thrust_macros::ghost!(|in_memory_order: IndexVec<u32, FieldIdx>| -> IndexVec<u32, FieldIdx> {
        in_memory_order
    });
    thrust_macros::proof!(lemmas::distinct_of_injective(order, n));
    let mut in_memory_order_a = IndexVec::<u32, FieldIdx>::new();
    let mut in_memory_order_b = IndexVec::<u32, FieldIdx>::new();
    for i in in_memory_order {
        thrust_macros::invariant!(
            |iter: std::vec::IntoIter<FieldIdx>,
             iter_old: thrust_models::Ghost<std::vec::IntoIter<FieldIdx>>,
             produced: thrust_models::Ghost<thrust_models::model::Seq<<FieldIdx as thrust_models::Model>::Ty>>,
             order: thrust_models::Ghost<IndexVec<u32, FieldIdx>>,
             in_memory_order_a: IndexVec<u32, FieldIdx>,
             in_memory_order_b: IndexVec<u32, FieldIdx>,
             n: usize,
             b_start: FieldIdx| {
                iter_old.0 == order
                    && iter_old.1 == 0
                    && order.len() == n
                    && <FieldIdx as Idx>::index_logic(b_start) <= n
                    && forall(|k: USize| 0 <= k && k <= n ==> <FieldIdx as Idx>::can_new(k))
                    && forall(|k: USize, i: USize|
                        0 <= k && k < n && <FieldIdx as Idx>::index_is(order[k], i) ==> i < n)
                    && lemmas::distinct::<FieldIdx>(order, n)
                    && in_memory_order_a.len() + in_memory_order_b.len() == produced.len()
                    && in_memory_order_b.len()
                        == lemmas::cnt_ge::<FieldIdx>(order, produced.len(), <FieldIdx as Idx>::index_logic(b_start))
                    && forall(|k: USize|
                        0 <= k && k < in_memory_order_b.len() ==> <FieldIdx as Idx>::index_logic(in_memory_order_b[k])
                                < n - <FieldIdx as Idx>::index_logic(b_start))
            }
        );
        if let Some(j) = i.index().checked_sub(b_start.index()) {
            in_memory_order_b.push(FieldIdx::new(j));
        } else {
            in_memory_order_a.push(i);
        }
    }
    thrust_macros::proof!(lemmas::permutation_split(order, n, b_start.index()));
    thrust_macros::proof!(lemmas::permutation_split_le(order, n, b_start.index()));
    (in_memory_order_a, in_memory_order_b)
}

// The specification of stage 7 (README.md of the stage files).
//
// Precondition (experiments/2026-10-01-layout-precondition-review.md), with n the number of
// saved locals (`local_layouts.len()`), V the number of variants and P the number of prefix
// layouts. rustc's caller (`rustc_ty_utils::layout`, from the `CoroutineLayout` that
// `rustc_mir_transform` builds) guarantees the first group; the second states invariants of
// rustc's data layouts and computed layouts; the third is stronger than what the caller
// guarantees and restricts the scope of the proof.
// - Guaranteed by the caller:
//   - V > 0 (V = 3 + the number of yields). Not a panic condition: `V - 1` wraps without overflow
//     checks, and Thrust checks that an unsigned subtraction stays non-negative;
//   - `storage_conflicts` is well formed with at most n rows, and every set bit's column is below
//     the ghost column bound, itself at most the number of rows (eligibility's `count(local_b)`
//     reads a column index as a row): an n by n matrix;
//   - every local a variant lists is below n;
//   - the index types can be built for every local (`LocalIdx` below n), up to V (`VariantIdx`;
//     `iter_enumerated` builds `new(V)`), and up to each variant's length (`FieldIdx`; a variant
//     may list a local twice);
//   - `tag_to_layout` accepts every integer scalar `Initialized { value: Int(_, false), .. }`
//     (`pre!`), the only scalars `layout()` passes; rustc's closure builds `LayoutData::scalar`,
//     which panics on a pointer scalar of an unknown address space.
// - Invariants of rustc's layouts: `dl_wf` of the data layout `calc.cx` names, which `univariant`
//   requires; `niche_wf` of the largest niche of every layout `univariant` may receive, and the
//   niche within that layout; `Scalar::wf_in` of every such layout whose `backend_repr` is a
//   scalar (`scalar_pair`). These layouts are each of `local_layouts` and `prefix_layouts`, and
//   `tag_to_layout`'s result for any such integer scalar (through its postcondition), each named by `post!` of
//   `Deref::deref`. `F`'s `deref` is a function (`deref_functional`), which `univariant`
//   requires; rustc's `Layout` dereferences to the interned pointer it holds.
// - Not guaranteed by the caller:
//   - `FieldIdx` can be built up to P + 1 + n (the prefix, the tag and at most n promoted
//     locals), and P + 1 + n <= u32::MAX, for the `u32` memory order. The panic condition is
//     P + 1 + c with c the number of ineligible locals (`DenseBitSet::card` of
//     `ineligible_locals`): c is computed inside, from eligibility's result, so a condition on
//     the inputs can only bound it by n. rustc's index types are bounded by 0xFFFF_FF00, so a
//     coroutine with P + 1 + n above that is excluded, also when P + 1 + c is not.
//   - The size bound: with T the weight (`weight`: each layout's size and twice its alignment)
//     of `prefix_layouts`, the tag's layout and all of `local_layouts`, plus the aggregate and
//     `i8` alignments 2^qa and 2^qi, 3T + 2^qa + 2^qi is below the object size bound b. It gives
//     `univariant`'s `fits_in_any_order` at both calls, the scope restriction of `univariant`
//     (layout.rs): rustc's caller passes any coroutine and handles `SizeOverflow`, which the
//     bound makes unreachable. It excludes coroutines whose layouts weigh about a third of b or
//     more (b = 2^15 on 16-bit targets). The prefix's fields are `prefix_layouts`, the tag and the
//     promoted locals, a subset of `local_layouts`, so their sum S_p (`weighs`, no prefix and no
//     `repr` alignment) is at most T. A variant's kind is `Prefixed` by the prefix's size, below
//     S_p, and alignment, at most S_p (univariant's ensures), so its sum is below its Assigned
//     locals' weight plus 3 S_p + 2^qa + 2^qi; its Assigned locals appear once each
//     (eligibility's property 2c) and are not promoted (property 4), so with the promoted ones
//     they weigh at most `local_layouts`' weight, and the sum is below 3T + 2^qa + 2^qi.
#[thrust_macros::requires(
    (*variant_fields).len() > 0
        && LayoutCalculator::<C>::deref_functional::<FieldIdx, VariantIdx, F>()
        && (*storage_conflicts).num_rows <= (*local_layouts).len()
        && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
        && BitMatrix::<LocalIdx, LocalIdx>::cols_below(*storage_conflicts, *(*storage_conflicts).col_bound)
        && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
        && forall(|v: usize, f: usize|
            0 <= v && v < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[v].len() ==> forall(|i: USize|
                <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i) ==> i < (*local_layouts).len()))
        && forall(|k: USize| 0 <= k && k < (*local_layouts).len() ==> <LocalIdx as Idx>::can_new(k))
        && forall(|k: USize| 0 <= k && k <= (*variant_fields).len() ==> <VariantIdx as Idx>::can_new(k))
        && forall(|k: USize|
            0 <= k && k <= prefix_layouts.len() + 1 + (*local_layouts).len() ==> <FieldIdx as Idx>::can_new(k))
        && forall(|v: usize, k: USize|
            0 <= v && v < (*variant_fields).len() && 0 <= k && k <= (*variant_fields)[v].len() ==> <FieldIdx as Idx>::can_new(k))
        && prefix_layouts.len() + 1 + (*local_layouts).len() <= 4294967295usize
        && forall(|dl: TargetDataLayout| C::dl_of(*calc, dl) ==> dl.default_address_space_pointer_spec.pointer_size.raw == 2
            || dl.default_address_space_pointer_spec.pointer_size.raw == 4
            || dl.default_address_space_pointer_spec.pointer_size.raw == 8)
        && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, z: Size|
            C::dl_of(*calc, dl)
                && 0 <= i
                && i < (*local_layouts).len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*local_layouts)[i]), d) && **d == l
                && l.largest_niche == Some(n) ==> (Niche::wf_in(n, dl) && (Primitive::size_in(n.value, dl, z) ==> n.offset.raw + z.raw <= l.size.raw)))
        && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, z: Size|
            C::dl_of(*calc, dl)
                && 0 <= i
                && i < prefix_layouts.len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&prefix_layouts[i]), d) && **d == l
                && l.largest_niche == Some(n) ==> (Niche::wf_in(n, dl) && (Primitive::size_in(n.value, dl, z) ==> n.offset.raw + z.raw <= l.size.raw)))
        && forall(|dl: TargetDataLayout, ti: Integer, tg: WrappingRange, s: Scalar, r: <F as thrust_models::Model>::Ty,
                l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, z: Size|
            C::dl_of(*calc, dl)
                && s == Scalar::Initialized { value: Primitive::Int(ti, false), valid_range: tg }
                && thrust_macros::post!(tag_to_layout(s), r)
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&r), d) && **d == l
                && l.largest_niche == Some(n) ==> (Niche::wf_in(n, dl) && (Primitive::size_in(n.value, dl, z) ==> n.offset.raw + z.raw <= l.size.raw)))
        && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, c: Scalar|
            C::dl_of(*calc, dl)
                && 0 <= i
                && i < (*local_layouts).len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*local_layouts)[i]), d) && **d == l
                && l.backend_repr == BackendRepr::Scalar(c) ==> Scalar::wf_in(c, dl))
        && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, c: Scalar|
            C::dl_of(*calc, dl)
                && 0 <= i
                && i < prefix_layouts.len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&prefix_layouts[i]), d) && **d == l
                && l.backend_repr == BackendRepr::Scalar(c) ==> Scalar::wf_in(c, dl))
        && forall(|dl: TargetDataLayout, ti: Integer, tg: WrappingRange, s: Scalar, r: <F as thrust_models::Model>::Ty,
                l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, c: Scalar|
            C::dl_of(*calc, dl)
                && s == Scalar::Initialized { value: Primitive::Int(ti, false), valid_range: tg }
                && thrust_macros::post!(tag_to_layout(s), r)
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&r), d) && **d == l
                && l.backend_repr == BackendRepr::Scalar(c) ==> Scalar::wf_in(c, dl))
        && forall(|ti: Integer, tg: WrappingRange| thrust_macros::pre!(tag_to_layout(Scalar::Initialized { value: Primitive::Int(ti, false), valid_range: tg })))
        && forall(|dl: TargetDataLayout, ti: Integer, tg: WrappingRange, s: Scalar, r: <F as thrust_models::Model>::Ty, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>|
            C::dl_of(*calc, dl) && s == Scalar::Initialized { value: Primitive::Int(ti, false), valid_range: tg } && thrust_macros::post!(tag_to_layout(s), r) && thrust_macros::post!(<F as core::ops::Deref>::deref(&r), d) && **d == l ==> exists(|wp: USize, wl: USize, q: USize, qa: USize, qi: USize, b: USize|
                    LayoutCalculator::<C>::weight::<FieldIdx, FieldIdx, VariantIdx, F>(&prefix_layouts, wp)
                        && LayoutCalculator::<C>::weight::<LocalIdx, FieldIdx, VariantIdx, F>(local_layouts, wl)
                        && q == l.align.abi.pow2
                        && qa == dl.aggregate_align.pow2
                        && qi == dl.i8_align.pow2
                        && ((dl.default_address_space_pointer_spec.pointer_size.raw == 2 && b == 32768u64)
                            || (dl.default_address_space_pointer_spec.pointer_size.raw == 4 && b == 2147483648u64)
                            || (dl.default_address_space_pointer_spec.pointer_size.raw == 8 && b == 2305843009213693952u64))
                        && 3 * (wp + pow2(q) * 2 + l.size.raw + wl + pow2(qa) + pow2(qi)) + pow2(qa) + pow2(qi) < b))
)]
#[thrust_macros::ensures(true)]
#[thrust_macros::context]
#[thrust::reveal(
    super::LayoutCalculator::fits_in_any_order,
    super::LayoutCalculator::weighs,
    super::super::Primitive::size_in,
    super::super::FieldsShape::arbitrary_of
)]
pub fn layout<
    'a,
    // `Ty: PartialEq`, as `fits_in_any_order` bounds it, for the two `assume!`s of it.
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    LocalIdx: Idx + thrust_models::Model,
    // Rewrite (rewrites.md S10): named, for the `requires` to call `C::dl_of` on.
    C: HasDataLayout,
>(
    calc: &LayoutCalculator<C>,
    local_layouts: &IndexSlice<LocalIdx, F>,
    mut prefix_layouts: IndexVec<FieldIdx, F>,
    variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>,
    storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>,
    tag_to_layout: impl Fn(Scalar) -> F,
) -> LayoutCalculatorResult<FieldIdx, VariantIdx, F> {
    use SavedLocalEligibility::*;

    let (ineligible_locals, assignments) =
        coroutine_saved_local_eligibility(local_layouts.len(), variant_fields, storage_conflicts);
    // The set's members are Ineligible (property 4), so with the locals Assigned to any one variant
    // they are at most n: the per-variant closure's `requires` at `Map::new`.
    thrust_macros::proof!(ones_assigned_disjoint(&ineligible_locals, &assignments, local_layouts.len()));
    thrust_macros::proof!(card_ones(&ineligible_locals));

    let tag_index = prefix_layouts.next_index();

    // `variant_fields.len() > 0` (the precondition) keeps the subtraction from wrapping.
    let max_discr = (variant_fields.len() - 1) as u128;
    let discr_int = Integer::fit_unsigned(max_discr);
    let tag = Scalar::Initialized {
        value: Primitive::Int(discr_int, false),
        valid_range: WrappingRange {
            start: 0,
            end: max_discr,
        },
    };

    // Rewrite (rewrites.md R8): `Map::new(it, f)` for `it.map(f)`, `extend_from` for `extend`.
    // The closure's contract, as that of the per-variant closure's map closure below: a member
    // of the set is a local below n, and the closure returns its layout.
    let promoted_layouts = Map::new(
        ineligible_locals.iter(),
        thrust_macros::closure!(
            captures(local_layouts: &mut &IndexSlice<LocalIdx, F>),
            requires(<LocalIdx as Idx>::index_logic(local) < (**local_layouts).len()),
            ensures(result == (**local_layouts)[<LocalIdx as Idx>::index_logic(local)]),
            |local: LocalIdx| -> F { local_layouts[local] },
        ),
    );
    prefix_layouts.push(tag_to_layout(tag));
    prefix_layouts.extend_from(promoted_layouts);
    // `push` and `extend_from` give `prefix_layouts.len() == P + 1 + c`, c the items
    // `ineligible_locals.iter()` yields (`Map` keeps the length), which is the set's count `card`:
    // `iter` starts `BitIter`'s `left` at it, and the iterator completes with nothing left.
    // Rewrite (rewrites.md R13): the `repr` argument is bound to a name, for the `assume!`.
    let repr = ReprOptions::default();
    // Assumed (not proved): `univariant`'s `fits_in_any_order` for the prefix. rustc's code makes
    // it true under `layout()`'s size bound: the prefix's fields are the entry `prefix_layouts`,
    // the tag's layout and the promoted locals, which are distinct locals (the set's members,
    // each yielded once, increasing), so their weight is at most that of `prefix_layouts`, the tag
    // and all of `local_layouts`, T in the size bound, and 3T + 2^qa + 2^qi < b gives the prefix's
    // weighs sum below b. Not proved: `weight` is an existential over a `Seq<Int>` of the fields'
    // weights, and no term builds the witness for a selection of `local_layouts` (a field's
    // weight is read through `deref`'s postcondition, a relation).
    thrust_macros::assume!(
        |calc: &LayoutCalculator<C>, prefix_layouts: IndexVec<FieldIdx, F>, repr: ReprOptions|
            LayoutCalculator::<C>::fits_in_any_order::<FieldIdx, VariantIdx, F>(*calc, &prefix_layouts, &repr, StructKind::AlwaysSized)
    );
    // Reachability twin of the `assume!` (fail root layout_reach.rs): the path after it is
    // reachable, so the `assume!` makes no proof here vacuous.
    #[cfg(thrust_layout_reach_prefix)]
    thrust_macros::proof_assert!(|| false);
    let prefix = calc.univariant(
        &prefix_layouts,
        &repr,
        StructKind::AlwaysSized,
    )?;

    let (prefix_size, prefix_align) = (prefix.size, prefix.align);

    let (outer_fields, promoted_offsets, promoted_memory_index) = match prefix.fields {
        FieldsShape::Arbitrary {
            mut offsets,
            in_memory_order,
        } => {
            let b_start = tag_index.plus(1);
            // `split_off(b_start.index())` needs `b_start.index() <= offsets.raw.len()`:
            // `b_start` is P + 1 (`next_index`, `plus`), and `offsets` has `prefix_layouts.len()`
            // entries (univariant's `arbitrary_of`), P + 1 + c by the prefix-length fact above.
            let offsets_b = IndexVec::from_raw(offsets.raw.split_off(b_start.index()));
            let offsets_a = offsets;

            // Rewrite (rewrites.md R11): the loop that splits the memory order at `b_start` is
            // `split_in_memory_order`. Its `requires` holds by univariant's `arbitrary_of` (the
            // order is a permutation of `0..n`, n = P + 1 + c) and `layout()`'s `requires`
            // (`FieldIdx` reaches n); its `ensures` gives the second part n - (P + 1) = c entries,
            // each below c: `invert_bijective_mapping` needs its entries below its length, and the
            // variants need `promoted_memory_index` to have c entries.
            let (in_memory_order_a, in_memory_order_b) =
                split_in_memory_order(in_memory_order, b_start, prefix_layouts.len());

            let outer_fields = FieldsShape::Arbitrary {
                offsets: offsets_a,
                in_memory_order: in_memory_order_a,
            };
            (
                outer_fields,
                offsets_b,
                // `invert_bijective_mapping` requires every element of `in_memory_order_b` below
                // its length, and `promoted_memory_index` gets at least n - (P + 1) = c entries:
                // the permutation split above.
                in_memory_order_b.invert_bijective_mapping(),
            )
        }
        // Unreachable by univariant's ensures (`arbitrary_of`).
        _ => unreachable!(),
    };

    let mut size = prefix.size;
    let mut align = prefix.align;
    // Rewrite (rewrites.md R8): `Map::new(it, f)` for `it.map(f)` and `Filter::new(it, p)` for
    // `it.filter(p)` here and below, and `collect_index_vec_result` for the `collect` at the end
    // of this expression.
    // The per-variant closure's contract: its `requires` states, of the variant it is given, what
    // its body reads of the captures. These are stage 5's properties 1, 2b, 2c and 3 at the
    // variant's entries, the lengths of the captures, the count c + (locals Assigned to the
    // variant) <= n that sites 1 and 3 need, and the conjuncts of `layout()`'s `requires` that the
    // variant's `univariant` call needs of `calc` and `local_layouts`. At `Map::new` the count
    // follows from c <= `card` of the ineligible set (the permutation split) and
    // `ones_assigned_disjoint`. The requires names no bit-set predicate: their bit arithmetic in
    // every cone of the closure leaves even `Filter::new`'s precondition without an answer. Its
    // `ensures` is `true`: `layout()` states nothing of the variants it returns. The closure is
    // `FnMut` (it updates `size` and `align`), so a clause reads each capture through the
    // receiver, as `&mut` of the type it is captured by. No `hist_inv` bounds `size` and `align`:
    // nothing after the `collect` needs a bound, as `Size::align_to` requires nothing
    // (`#[thrust::callable]`, its body checked by the `values.rs` root) and `max` neither.
    let variants = collect_index_vec_result::<VariantIdx, _, _, _>(Map::new(
        variant_fields.iter_enumerated(),
        thrust_macros::closure!(
        captures(
            calc: &mut &LayoutCalculator<C>,
            local_layouts: &mut &IndexSlice<LocalIdx, F>,
            assignments: &mut &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
            promoted_offsets: &mut &IndexVec<FieldIdx, Size>,
            promoted_memory_index: &mut &IndexVec<FieldIdx, u32>,
        ),
        requires(
            (**assignments).len() == (**local_layouts).len()
                && forall(|k: USize| !(0 <= k && k <= (*variant_fields).len()) || <FieldIdx as Idx>::can_new(k))
                && forall(|f: usize|
                    !(0 <= f && f < (*variant_fields).len())
                    || forall(|i: USize|
                        !<LocalIdx as Idx>::index_is((*variant_fields)[f], i) || i < (**local_layouts).len()))
                // Property 1 at the variant's entries.
                && forall(|l: usize, f: usize|
                    !(0 <= l && l < (**assignments).len()
                        && 0 <= f && f < (*variant_fields).len()
                        && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i)))
                    || (**assignments)[l] != SavedLocalEligibility::Unassigned)
                // Property 2b: a local the variant lists is Assigned to the variant, if at all.
                && forall(|l: usize, f: usize, vi: <VariantIdx as thrust_models::Model>::Ty, w: USize|
                    !(0 <= l && l < (**assignments).len()
                        && 0 <= f && f < (*variant_fields).len()
                        && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i))
                        && (**assignments)[l] == SavedLocalEligibility::Assigned(vi)
                        && <VariantIdx as Idx>::index_is(index, w))
                    || forall(|vn: USize| !<VariantIdx as Idx>::index_is(vi, vn) || vn == w))
                // Property 2c: an Assigned local appears once in the variant's entries.
                && forall(|l: usize, f: usize, g: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    !(0 <= l && l < (**assignments).len()
                        && 0 <= f && f < (*variant_fields).len()
                        && 0 <= g && g < (*variant_fields).len()
                        && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i))
                        && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[g], i))
                        && (**assignments)[l] == SavedLocalEligibility::Assigned(vi))
                    || f == g)
                // Property 3, with the set's count c read as the promoted fields' count: an
                // ineligible local's field index is below it.
                && forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    !(0 <= l && l < (**assignments).len()
                        && (**assignments)[l] == SavedLocalEligibility::Ineligible(x))
                    || exists(|k: <FieldIdx as thrust_models::Model>::Ty|
                        x == Some(k)
                            && forall(|i: USize|
                                !<FieldIdx as Idx>::index_is(k, i)
                                    || (i < (**promoted_offsets).len() && i < (**promoted_memory_index).len()))))
                // Sites 1 and 3: the promoted fields' count c and the locals Assigned to the
                // variant are no more than the n locals (`ones_assigned_disjoint` and the
                // permutation split), and `FieldIdx` and `u32` reach n.
                && (**promoted_memory_index).len()
                    + counts::class_cnt::<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                        **assignments, (**assignments).len(), SavedLocalEligibility::Assigned(index))
                    <= (**assignments).len()
                && forall(|k: USize| !(0 <= k && k <= (**local_layouts).len()) || <FieldIdx as Idx>::can_new(k))
                && (**local_layouts).len() <= 4294967295usize
                // `univariant`'s `layout_pre` and `deref_functional` at the variant's fields,
                // which are entries of `local_layouts`.
                && LayoutCalculator::<C>::deref_functional::<FieldIdx, VariantIdx, F>()
                && forall(|z: USize| !(z == 0usize) || <VariantIdx as Idx>::can_new(z))
                && forall(|dl: TargetDataLayout| !C::dl_of(**calc, dl)
                    || dl.default_address_space_pointer_spec.pointer_size.raw == 2
                    || dl.default_address_space_pointer_spec.pointer_size.raw == 4
                    || dl.default_address_space_pointer_spec.pointer_size.raw == 8)
                && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, z: Size|
                    !(C::dl_of(**calc, dl)
                        && 0 <= i
                        && i < (**local_layouts).len()
                        && thrust_macros::post!(<F as core::ops::Deref>::deref(&(**local_layouts)[i]), d) && **d == l
                        && l.largest_niche == Some(n))
                        || (Niche::wf_in(n, dl) && (!Primitive::size_in(n.value, dl, z) || n.offset.raw + z.raw <= l.size.raw)))
                && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, c: Scalar|
                    !(C::dl_of(**calc, dl)
                        && 0 <= i
                        && i < (**local_layouts).len()
                        && thrust_macros::post!(<F as core::ops::Deref>::deref(&(**local_layouts)[i]), d) && **d == l
                        && l.backend_repr == BackendRepr::Scalar(c))
                        || Scalar::wf_in(c, dl))
        ),
        ensures(true),
        |(index, variant_fields): (VariantIdx, &IndexVec<FieldIdx, LocalIdx>)|
            -> Result<VariantLayout<FieldIdx>, crate::rustc_abi::layout::LayoutCalculatorError<F>> {
            // Rewrite (rewrites.md R14): the variant's fields, the layouts of the entries whose local
            // is Assigned to the variant, are collected by `variant_field_layouts`. Its `requires`
            // holds by the closure's `requires`; its `ensures` gives the count sites 1 and 3 need
            // (with the closure's `requires` on c) and that each field is a layout of
            // `local_layouts`, which `univariant`'s `layout_pre` reads.
            let fields = variant_field_layouts(variant_fields, &assignments, index, local_layouts);

            // Rewrite (rewrites.md R13): `calc` and the arguments are bound to names, for the
            // `assume!`, which names local variables only (not a closure's captures).
            let calc_ref = calc;
            let repr = ReprOptions::default();
            let kind = StructKind::Prefixed(prefix_size, prefix_align.abi);
            // Assumed (not proved): `univariant`'s `fits_in_any_order` for the variant. rustc's
            // code makes it true under `layout()`'s size bound (its header comment): the variant's
            // weighs sum is the weight of its fields plus the prefix's size and twice its
            // alignment, each below the prefix's weighs sum S_p (univariant's `ensures`), so it is
            // below (Assigned) + 3 S_p + 2^qa + 2^qi, with (Assigned) the weight of the variant's
            // fields. Those are the locals Assigned to the variant, each once (properties 2b and
            // 2c). S_p is at most the weight of the entry `prefix_layouts`, the tag and the promoted
            // locals, and the promoted locals are Ineligible (property 4), so disjoint from the
            // Assigned ones: (Assigned) + 3 (promoted) <= 3 (weight of `local_layouts`), and the sum
            // is below 3T + 2^qa + 2^qi < b. Not proved: as at the prefix, no term builds the
            // witness of `weight` for the fields the filter selects.
            thrust_macros::assume!(
                |calc_ref: &LayoutCalculator<C>, fields: IndexVec<FieldIdx, F>, repr: ReprOptions, kind: StructKind|
                    LayoutCalculator::<C>::fits_in_any_order::<FieldIdx, VariantIdx, F>(*calc_ref, &fields, &repr, kind)
            );
            // Reachability twin of the `assume!` (fail root layout_reach.rs): the path after it is
            // reachable, so the `assume!` makes no proof here vacuous.
            #[cfg(thrust_layout_reach_variant)]
            thrust_macros::proof_assert!(|| false);
            let mut variant = calc_ref.univariant(&fields, &repr, kind)?;

            let FieldsShape::Arbitrary {
                offsets,
                in_memory_order,
            } = variant.fields
            else {
                // Unreachable, as the prefix's above.
                unreachable!();
            };

            // Rewrite (rewrites.md R12): the combination of the variant's offsets and memory order
            // with the promoted ones is `combine_offsets`. Its `requires` holds by univariant's
            // `arbitrary_of` (m offsets, and the memory order a permutation of `0..m`), by
            // `filter_count` above with the closure's `requires` on c (c + m <= n, so `FieldIdx`
            // and `u32` reach c + m), and by the closure's `requires` (properties 1 and 3 and the
            // bounds of the variant's entries).
            let (combined_offsets, combined_in_memory_order) = combine_offsets(
                variant_fields,
                &assignments,
                &promoted_offsets,
                &promoted_memory_index,
                offsets,
                in_memory_order,
            );

            variant.fields = FieldsShape::Arbitrary {
                offsets: combined_offsets,
                in_memory_order: combined_in_memory_order,
            };

            size = size.max(variant.size);
            align = align.max(variant.align);
            // `VariantLayout::from_layout` requires `Arbitrary` fields: `variant.fields` was just
            // reassigned to them above.
            Ok(VariantLayout::from_layout(variant))
        },
        ),
    ))?;

    size = size.align_to(align.abi);

    // Rewrite (rewrites.md R8): `iter_all(it, f)` for `it.all(f)`.
    let uninhabited = prefix.uninhabited || iter_all(variants.iter(), |v| v.is_uninhabited());
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
