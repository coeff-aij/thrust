use crate::thrust_models;
use thrust_models::{exists, forall};

use crate::rustc_abi::layout::{LayoutCalculator, LayoutCalculatorResult, LayoutRef};
use crate::rustc_abi::{
    BackendRepr, FieldsShape, HasDataLayout, Integer, LayoutData, Niche, Primitive, ReprOptions,
    Scalar, StructKind, TagEncoding, TargetDataLayout, VariantLayout, Variants, WrappingRange,
};
use crate::rustc_index::bit_set::{BitIter, BitMatrix, DenseBitSet};
use crate::rustc_index::{Idx, IdxRange, IndexSlice, IndexVec, IterEnumerated, SliceIter};
use crate::case_study::USize;
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
        !(0 <= v && v < (*variant_fields).len()
            && 0 <= f && f < (*variant_fields)[v].len())
        || forall(|i: USize|
            !<LocalIdx as Idx>::index_is((*variant_fields)[v][f], i)
                || i < nb_locals))
    // `count(local_b)` takes a column index as a row, so every set bit's column must be below
    // the number of rows: the panic condition, through the matrix's ghost column bound.
    && (*storage_conflicts).num_rows <= nb_locals
    && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
    && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
    && forall(|k: USize| !(0 <= k && k < nb_locals) || LocalIdx::can_new(k))
    && forall(|n: USize| !(0 <= n && n <= nb_locals) || FieldIdx::can_new(n))
    && forall(|v: USize| !(0 <= v && v <= (*variant_fields).len()) || VariantIdx::can_new(v))
)]
#[thrust_macros::ensures(
    // `assignments` has one entry per local, and `inel` is a set over the locals, so its
    // iterator yields locals below `nb_locals`.
    result.1.len() == nb_locals
    && result.0.0 == nb_locals
    // 1. Unassigned locals never appear in any variant's field list.
    && forall(|l: usize| !(0 <= l && l < nb_locals && result.1[l] == SavedLocalEligibility::Unassigned)
        || forall(|v: usize, f: usize|
            !(0 <= v && v < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[v].len())
            || !thrust_models::exists(|i: USize|
                i == l
                    && <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i))))
    // 2. An Assigned(v) local appears in variant v's field list.
    && forall(|l: usize, v: usize|
        !(0 <= l && l < nb_locals
            && thrust_models::exists(|vi: <VariantIdx as thrust_models::Model>::Ty|
                thrust_models::exists(|vn: USize| vn == v && <VariantIdx as Idx>::index_is(vi, vn))
                    && result.1[l] == SavedLocalEligibility::Assigned(vi)))
        || (v < (*variant_fields).len()
            && thrust_models::exists(|f: usize|
                0 <= f && f < (*variant_fields)[v].len()
                    && thrust_models::exists(|i: USize|
                        i == l
                            && <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i)))))
    // 2b. A local a variant lists is Assigned to that variant if it is Assigned at all, which
    // `layout()`'s `Assigned(_) => unreachable!()` needs.
    && forall(|l: usize, w: usize, f: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
        !(0 <= l && l < nb_locals
            && 0 <= w && w < (*variant_fields).len()
            && 0 <= f && f < (*variant_fields)[w].len()
            && thrust_models::exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][f], i))
            && result.1[l] == SavedLocalEligibility::Assigned(vi))
        || forall(|vn: USize| !<VariantIdx as Idx>::index_is(vi, vn) || vn == w))
    // 2c. An Assigned local appears at most once in a variant's field list: rustc's pass makes a
    // local it sees a second time ineligible. `layout()` counts a variant's Assigned locals by it.
    && forall(|l: usize, w: usize, f: usize, g: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
        !(0 <= l && l < nb_locals
            && 0 <= w && w < (*variant_fields).len()
            && 0 <= f && f < (*variant_fields)[w].len()
            && 0 <= g && g < (*variant_fields)[w].len()
            && thrust_models::exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][f], i))
            && thrust_models::exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][g], i))
            && result.1[l] == SavedLocalEligibility::Assigned(vi))
        || f == g)
    // 3. An ineligible local has its promoted field index, below the number of members of
    // `inel` (its ghost count `result.0.3`, the position in `inel.iter()`'s enumeration).
    && forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
        !(0 <= l && l < nb_locals && result.1[l] == SavedLocalEligibility::Ineligible(x))
        || thrust_models::exists(|k: <FieldIdx as thrust_models::Model>::Ty|
            x == Some(k) && forall(|i: USize| !<FieldIdx as Idx>::index_is(k, i) || i < result.0.3)))
    // 4. Membership in `inel` matches being `Ineligible(_)`, written as an `<==>` via two `==>`.
    // `mem` takes an `Int` (its declared `usize` parameter is lowered to
    // `Int` by `#[thrust_macros::predicate]`, see the note above the
    // `requires`), but real `Vec` indexing needs a literal `usize`; the
    // `exists(|li: Int| li == l && ..)` below is a `usize -> Int` bridge
    // (`Int: PartialEq<T> where T: Model<Ty = Int>`, and `usize` is one).
    && forall(|l: usize| !(0 <= l && l < nb_locals) ||
        (!thrust_models::exists(|li: USize| li == l && DenseBitSet::<LocalIdx>::mem(result.0, li))
            || thrust_models::exists(|x: Option<<FieldIdx as thrust_models::Model>::Ty>| result.1[l] == SavedLocalEligibility::Ineligible(x))))
    && forall(|l: usize| !(0 <= l && l < nb_locals) ||
        (!thrust_models::exists(|x: Option<<FieldIdx as thrust_models::Model>::Ty>| result.1[l] == SavedLocalEligibility::Ineligible(x))
            || thrust_models::exists(|li: USize| li == l && DenseBitSet::<LocalIdx>::mem(result.0, li))))
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
            && 0 <= ineligible_locals.3
            && ineligible_locals.3 <= ineligible_locals.0
            && variants.1 >= 0 && variants.1 <= variants.0.len() && *variants.0 == *variant_fields
            && forall(|v: USize| !(0 <= v && v <= (*variant_fields).len()) || <VariantIdx as Idx>::can_new(v))
            && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                || i < (*variant_fields).len())
            && (*storage_conflicts).num_rows <= nb_locals.at_entry()
            && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
            && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
            && forall(|k: USize| !(0 <= k && k < nb_locals.at_entry()) || <LocalIdx as Idx>::can_new(k))
            && forall(|n: USize| !(0 <= n && n <= nb_locals.at_entry()) || <FieldIdx as Idx>::can_new(n))
            && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x))
                || (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
            && forall(|l: USize| !(0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                || assignments[l] == SavedLocalEligibility::Ineligible(None))
        );
        thrust_macros::invariant!(
            |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variants: IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
            *variants.0 == *variant_fields.at_entry()
            && forall(|v: USize, f: USize| !(0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len())
                || forall(|i: USize| !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], i) || i < nb_locals.at_entry()))
            && forall(|l: USize, v: USize, f: USize|
                !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                    && 0 <= v && v < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[v].len())
                || !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
            && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                || (i < (*variant_fields.at_entry()).len()
                    && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
            && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                    && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                    && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn))
                || vn == w)
            && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                    && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                    && assignments[l] == SavedLocalEligibility::Assigned(vi))
                || f == g)
        );
        for local in fields {
            // `variant_index` is the variant at `variants.1 - 1`, whose fields `iter` walks;
            // property 1 covers the variants before it and its locals before `iter.1`.
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, variants: IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, iter: SliceIter<LocalIdx>, variant_index: VariantIdx, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>, nb_locals: thrust_models::FnParam<usize>|
                assignments.len() == nb_locals.at_entry()
                && ineligible_locals.0 == nb_locals.at_entry()
                && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                && 0 <= ineligible_locals.3
                && ineligible_locals.3 <= ineligible_locals.0
                && variants.1 >= 0 && variants.1 <= variants.0.len() && *variants.0 == *variant_fields
                && forall(|v: USize| !(0 <= v && v <= (*variant_fields).len()) || <VariantIdx as Idx>::can_new(v))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                    || i < (*variant_fields).len())
                && (*storage_conflicts).num_rows <= nb_locals.at_entry()
                && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
                && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
                && forall(|k: USize| !(0 <= k && k < nb_locals.at_entry()) || <LocalIdx as Idx>::can_new(k))
                && forall(|n: USize| !(0 <= n && n <= nb_locals.at_entry()) || <FieldIdx as Idx>::can_new(n))
                && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x))
                    || (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
                && forall(|l: USize| !(0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                    || assignments[l] == SavedLocalEligibility::Ineligible(None))
                && iter.1 >= 0 && iter.1 <= iter.0.len()
                && forall(|k: USize| !(0 <= k && k < iter.0.len())
                    || forall(|i: USize| !<LocalIdx as Idx>::index_is(iter.0[k], i) || i < nb_locals.at_entry()))
                && forall(|i: USize| !<VariantIdx as Idx>::index_is(variant_index, i) || i < (*variant_fields).len())
                && forall(|p: USize| !<VariantIdx as Idx>::index_is(variant_index, p) || p + 1 == variants.1)
            );
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variants: IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, iter: SliceIter<LocalIdx>, variant_index: VariantIdx, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
                *variants.0 == *variant_fields.at_entry()
                && forall(|v: USize, f: USize| !(0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len())
                    || forall(|i: USize| !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], i) || i < nb_locals.at_entry()))
                && forall(|p: USize| !<VariantIdx as Idx>::index_is(variant_index, p) || *iter.0 == (*variant_fields.at_entry())[p])
                && forall(|l: USize, v: USize, f: USize|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v + 1 < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[v].len())
                    || !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|l: USize, k: USize|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned && 0 <= k && k < iter.1)
                    || !<LocalIdx as Idx>::index_is(iter.0[k], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                    || (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w + 1 < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn))
                    || vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w + 1 < variants.1 && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi))
                    || f == g)
                && forall(|l: USize, k: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= k && k < iter.1 && <LocalIdx as Idx>::index_is(iter.0[k], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn))
                    || vn + 1 == variants.1)
                && forall(|l: USize, j: USize, k: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= j && j < iter.1 && 0 <= k && k < iter.1
                        && <LocalIdx as Idx>::index_is(iter.0[j], l) && <LocalIdx as Idx>::index_is(iter.0[k], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi))
                    || j == k)
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
            && 0 <= ineligible_locals.3
            && ineligible_locals.3 <= ineligible_locals.0
            && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                || i < (*variant_fields).len())
            && (*storage_conflicts).num_rows <= nb_locals.at_entry()
            && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
            && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
            && forall(|k: USize| !(0 <= k && k < nb_locals.at_entry()) || <LocalIdx as Idx>::can_new(k))
            && forall(|n: USize| !(0 <= n && n <= nb_locals.at_entry()) || <FieldIdx as Idx>::can_new(n))
            && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x))
                || (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
            && forall(|l: USize| !(0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                || assignments[l] == SavedLocalEligibility::Ineligible(None))
            && rows.start >= 0 && rows.end == (*storage_conflicts).num_rows
        );
        thrust_macros::invariant!(
            |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
            forall(|l: USize, v: USize, f: USize|
                !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                    && 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len())
                || !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
            && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                || (i < (*variant_fields.at_entry()).len()
                    && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
            && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                    && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                    && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn))
                || vn == w)
            && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                    && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                    && assignments[l] == SavedLocalEligibility::Assigned(vi))
                || f == g)
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
                && 0 <= ineligible_locals.3
                && ineligible_locals.3 <= ineligible_locals.0
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                    || i < (*variant_fields).len())
                && (*storage_conflicts).num_rows <= nb_locals.at_entry()
                && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
                && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
                && forall(|k: USize| !(0 <= k && k < nb_locals.at_entry()) || <LocalIdx as Idx>::can_new(k))
                && forall(|n: USize| !(0 <= n && n <= nb_locals.at_entry()) || <FieldIdx as Idx>::can_new(n))
                && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x))
                    || (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
                && forall(|l: USize| !(0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                    || assignments[l] == SavedLocalEligibility::Ineligible(None))
                && rows.start >= 0 && rows.end == (*storage_conflicts).num_rows
                && forall(|i: USize| !<LocalIdx as Idx>::index_is(local_a, i) || i < nb_locals.at_entry())
                && iter.4 == *(*storage_conflicts).col_bound
                && 0 <= iter.5 && 0 <= iter.6 && iter.5 + iter.6 <= iter.4
            );
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
                forall(|l: USize, v: USize, f: USize|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len())
                    || !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                    || (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn))
                    || vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi))
                    || f == g)
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
                    !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                    || i < used_variants.0)
                && assignments.len() == nb_locals.at_entry()
                && ineligible_locals.0 == nb_locals.at_entry()
                && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                && 0 <= ineligible_locals.3
                && ineligible_locals.3 <= ineligible_locals.0
                && forall(|k: USize| !(0 <= k && k < nb_locals.at_entry()) || <LocalIdx as Idx>::can_new(k))
                && forall(|n: USize| !(0 <= n && n <= nb_locals.at_entry()) || <FieldIdx as Idx>::can_new(n))
                && forall(|l: USize, v: USize, f: USize|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len())
                    || !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                    || (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn))
                    || vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi))
                    || f == g)
                && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x))
                    || (DenseBitSet::<LocalIdx>::mem(ineligible_locals, l) && x == None))
                && forall(|l: USize| !(0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                    || assignments[l] == SavedLocalEligibility::Ineligible(None))
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
                    && forall(|k: USize| !(0 <= k && k < iter.2) || iter.1[k] == SavedLocalEligibility::Ineligible(None))
                    && ineligible_locals.0 == nb_locals.at_entry()
                    && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                    && 0 <= ineligible_locals.3
                    && ineligible_locals.3 <= ineligible_locals.0
                    && forall(|k: USize| !(0 <= k && k < nb_locals.at_entry()) || <LocalIdx as Idx>::can_new(k))
                    && forall(|n: USize| !(0 <= n && n <= nb_locals.at_entry()) || <FieldIdx as Idx>::can_new(n))
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
                && 0 <= ineligible_locals.3
                && ineligible_locals.3 <= ineligible_locals.0
                && iter.0.4 == ineligible_locals.0 && iter.1 == iter.0.5
                && 0 <= iter.1 && iter.1 <= iter.0.4
                && 0 <= iter.0.6 && iter.0.5 + iter.0.6 == ineligible_locals.3
                && forall(|k: USize| !(0 <= k && k < nb_locals.at_entry()) || <LocalIdx as Idx>::can_new(k))
                && forall(|n: USize| !(0 <= n && n <= nb_locals.at_entry()) || <FieldIdx as Idx>::can_new(n))
                && forall(|l: USize, v: USize, f: USize|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len())
                    || !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    !(0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i))
                    || (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn))
                    || vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    !(0 <= l && l < nb_locals.at_entry() && 0 <= w && w < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi))
                    || f == g)
                && forall(|l: USize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
                    !(0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Ineligible(x))
                    || DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                && forall(|l: USize| !(iter.0.7[l] != 0) || DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                && forall(|l: USize| !(0 <= l && l < nb_locals.at_entry() && DenseBitSet::<LocalIdx>::mem(ineligible_locals, l))
                    || (iter.0.7[l] != 0 && assignments[l] == SavedLocalEligibility::Ineligible(None))
                    || exists(|k: <FieldIdx as thrust_models::Model>::Ty| assignments[l] == SavedLocalEligibility::Ineligible(Some(k))
                        && forall(|i: USize| !<FieldIdx as Idx>::index_is(k, i) || i < ineligible_locals.3)))
            );
            assignments[local] = Ineligible(Some(FieldIdx::new(idx)));
        }
    }

    (ineligible_locals, assignments)
}

// The specification of stage 7 (README.md of the stage files).
//
// Precondition (experiments/2026-10-01-layout-precondition-review.md), with n the number of
// saved locals (`local_layouts.len()`), V the number of variants and P the number of prefix
// layouts:
// - V > 0, which rustc's caller has by construction (V = 3 + the number of yields);
// - `storage_conflicts` is well formed, has at most n rows, and every set bit's column is below
//   the number of rows (eligibility's `count(local_b)` reads a column index as a row);
// - every local a variant lists is below n;
// - the index types can be built wherever `new` is called: `LocalIdx` below n, `VariantIdx` up
//   to V (`iter_enumerated` builds `new(V)`), `FieldIdx` up to P + 1 + n (the prefix, the tag
//   and at most n promoted locals) and up to each variant's length (a variant may list a local
//   twice);
// - P + 1 + n <= u32::MAX, for the `u32` memory order.
//   Both P + 1 + n bounds are stronger than the panic condition, which is P + 1 + c with c the
//   number of ineligible locals (the ghost count of `ineligible_locals`): c is computed inside,
//   from eligibility's result, so a condition on the inputs can only bound it by n. rustc's
//   caller guarantees neither form.
// - `dl_wf` of the data layout `calc.cx` names, which `univariant` requires.
// - `niche_wf` of the largest niche of every layout `univariant` may receive: each of
//   `local_layouts` and `prefix_layouts`, and `tag_to_layout`'s result for any scalar (through
//   its postcondition), each named by `LayoutRef::layout_is`.
#[thrust_macros::requires(
    (*variant_fields).len() > 0
        && (*storage_conflicts).num_rows <= (*local_layouts).len()
        && *(*storage_conflicts).col_bound <= (*storage_conflicts).num_rows
        && BitMatrix::<LocalIdx, LocalIdx>::wf(*storage_conflicts)
        && forall(|v: usize, f: usize|
            !(0 <= v && v < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[v].len())
            || forall(|i: USize|
                !<LocalIdx as Idx>::index_is((*variant_fields)[v][f], i)
                    || i < (*local_layouts).len()))
        && forall(|k: USize| !(0 <= k && k < (*local_layouts).len()) || <LocalIdx as Idx>::can_new(k))
        && forall(|k: USize| !(0 <= k && k <= (*variant_fields).len()) || <VariantIdx as Idx>::can_new(k))
        && forall(|k: USize|
            !(0 <= k && k <= prefix_layouts.len() + 1 + (*local_layouts).len())
                || <FieldIdx as Idx>::can_new(k))
        && forall(|v: usize, k: USize|
            !(0 <= v && v < (*variant_fields).len() && 0 <= k && k <= (*variant_fields)[v].len())
                || <FieldIdx as Idx>::can_new(k))
        && prefix_layouts.len() + 1 + (*local_layouts).len() <= 4294967295usize
        && forall(|dl: TargetDataLayout| !C::dl_of(*calc, dl)
            || dl.default_address_space_pointer_spec.pointer_size.raw == 2
            || dl.default_address_space_pointer_spec.pointer_size.raw == 4
            || dl.default_address_space_pointer_spec.pointer_size.raw == 8)
        && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, n: Niche|
            !(C::dl_of(*calc, dl)
                && 0 <= i
                && i < (*local_layouts).len()
                && F::layout_is((*local_layouts)[i], l)
                && l.largest_niche == Some(n))
                || Niche::wf_in(n, dl))
        && forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, n: Niche|
            !(C::dl_of(*calc, dl)
                && 0 <= i
                && i < prefix_layouts.len()
                && F::layout_is(prefix_layouts[i], l)
                && l.largest_niche == Some(n))
                || Niche::wf_in(n, dl))
        && forall(|dl: TargetDataLayout, s: Scalar, r: <F as thrust_models::Model>::Ty,
                l: LayoutData<FieldIdx, VariantIdx>, n: Niche|
            !(C::dl_of(*calc, dl)
                && thrust_macros::post!(tag_to_layout(s), r)
                && F::layout_is(r, l)
                && l.largest_niche == Some(n))
                || Niche::wf_in(n, dl))
)]
#[thrust_macros::ensures(true)]
pub fn layout<
    'a,
    // Rewrite (rewrites.md S10): `LayoutRef` for `core::ops::Deref<Target = &'a LayoutData<..>>`.
    F: LayoutRef<'a, FieldIdx, VariantIdx> + core::fmt::Debug + Copy + PartialEq + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    LocalIdx: Idx + thrust_models::Model<Ty: PartialEq>,
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
    let promoted_layouts = Map::new(ineligible_locals.iter(), |local| local_layouts[local]);
    prefix_layouts.push(tag_to_layout(tag));
    prefix_layouts.extend_from(promoted_layouts);
    // `push` and `extend_from` give `prefix_layouts.len() == P + 1 + c`, c the items
    // `ineligible_locals.iter()` yields (`Map` keeps the length), which is the set's ghost count:
    // `iter` starts `BitIter`'s `left` at it, and the iterator completes with nothing left.
    let prefix = calc.univariant(
        &prefix_layouts,
        &ReprOptions::default(),
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
            // TODO(proof): the loop below has no invariant, so inference must find that the two
            // orders together hold at most as many entries as were read (each `push` needs
            // `u32::can_new` of the length) and that `j` is below `n - b_start`
            // (`FieldIdx::new(j)`).
            let offsets_b = IndexVec::from_raw(offsets.raw.split_off(b_start.index()));
            let offsets_a = offsets;

            let mut in_memory_order_a = IndexVec::<u32, FieldIdx>::new();
            let mut in_memory_order_b = IndexVec::<u32, FieldIdx>::new();
            for i in in_memory_order {
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
                // TODO(proof): `invert_bijective_mapping` requires every element of
                // `in_memory_order_b` below its length, and the variants need that length to be
                // c: the permutation split, which `lemma_permutation_split` below states of a
                // value it returns and not of `in_memory_order_b` (not called).
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
    let variants = collect_index_vec_result::<VariantIdx, _, _, _>(Map::new(
        variant_fields.iter_enumerated(),
        |(index, variant_fields)| {
            let variant_only_tys = Map::new(
                Filter::new(variant_fields.iter(), |local| match assignments[**local] {
                    // Unreachable by eligibility.rs's stage-5 property 1 (an `Unassigned` local
                    // never appears in any variant's field list).
                    Unassigned => unreachable!(),
                    Assigned(v) if v == index => true,
                    // Unreachable by property 2b (a listed local is Assigned to its own variant)
                    // and `Idx::index_is_injective` (`v == index`).
                    Assigned(_) => unreachable!(),
                    Ineligible(_) => false,
                }),
                |local| local_layouts[*local],
            );

            // Rewrite (rewrites.md R8): `collect_index_vec` for `collect`.
            let mut variant = calc.univariant(
                &collect_index_vec(variant_only_tys),
                &ReprOptions::default(),
                StructKind::Prefixed(prefix_size, prefix_align.abi),
            )?;

            let FieldsShape::Arbitrary {
                offsets,
                in_memory_order,
            } = variant.fields
            else {
                // Unreachable, as the prefix's above.
                unreachable!();
            };

            // TODO(proof): `invert_bijective_mapping` needs `u32::can_new` up to the number of
            // fields m, and `FieldIdx::new(invalid_field_idx)` needs `FieldIdx::can_new(c + m)`:
            // both need m, the variant's Assigned locals, bounded by the distinct locals
            // (c + m <= n). It holds by eligibility's property 2c (an Assigned local appears once
            // in its variant) and property 4 (the c ineligible locals are not Assigned), but it is
            // a count of distinct locals, which no contract states.
            let memory_index = in_memory_order.invert_bijective_mapping();
            let invalid_field_idx = promoted_memory_index.len() + memory_index.len();
            let mut combined_in_memory_order =
                IndexVec::from_elem_n(FieldIdx::new(invalid_field_idx), invalid_field_idx);

            let mut offsets_and_memory_index = iter::zip(offsets, memory_index);
            // Rewrite (rewrites.md R8): `Map::new` and `collect_index_vec` for `map` and `collect`.
            let combined_offsets = collect_index_vec(Map::new(
                variant_fields.iter_enumerated(),
                |(i, local)| {
                    let (offset, memory_index) = match assignments[*local] {
                        // Unreachable, as above.
                        Unassigned => unreachable!(),
                        Assigned(_) => {
                            // TODO(proof): `.unwrap()` needs
                            // `offsets_and_memory_index` to have as many
                            // entries left as there are `Assigned` locals
                            // still to visit -- README stage 7, "the number of Assigned
                            // equals the length of variant_only_tys".
                            let (offset, memory_index) = offsets_and_memory_index.next().unwrap();
                            (offset, promoted_memory_index.len() as u32 + memory_index)
                        }
                        Ineligible(field_idx) => {
                            // `.unwrap()`: `field_idx == Some(_)` by eligibility.rs's stage-5
                            // property 3.
                            let field_idx = field_idx.unwrap();
                            (
                                // `field_idx` is below the set's ghost count c (property 3),
                                // which is `offsets_b.len()` (the prefix length and `split_off`).
                                // TODO(proof): `promoted_memory_index` has c entries only by
                                // the permutation split above.
                                promoted_offsets[field_idx],
                                promoted_memory_index[field_idx],
                            )
                        }
                    };
                    // TODO(proof): `combined_in_memory_order[memory_index]`
                    // needs `promoted_memory_index.len() + memory_index <
                    // invalid_field_idx` -- README stage 7 (memory_index is a
                    // permutation's inverse, so `< len`; promoted_memory_index
                    // entries are likewise `< len`).
                    combined_in_memory_order[memory_index] = i;
                    offset
                },
            ));

            combined_in_memory_order
                .raw
                .retain(|&i| i.index() != invalid_field_idx);

            variant.fields = FieldsShape::Arbitrary {
                offsets: combined_offsets,
                in_memory_order: combined_in_memory_order,
            };

            size = size.max(variant.size);
            align = align.max(variant.align);
            // `VariantLayout::from_layout`'s own panic is unreachable: `variant.fields` was just
            // reassigned to `Arbitrary` above.
            Ok(VariantLayout::from_layout(variant))
        },
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
