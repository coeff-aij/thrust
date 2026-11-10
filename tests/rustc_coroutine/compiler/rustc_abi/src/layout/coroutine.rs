// `thrust_eligibility_fail` is set only by the fail twin of the eligibility root (`set_assignment`).
#![allow(unexpected_cfgs)]
use crate::thrust_models;
use thrust_models::model::BitVec;
use thrust_models::{exists, forall};

use crate::rustc_abi::layout::{LayoutCalculator, LayoutCalculatorResult, pow2};
use crate::rustc_abi::{
    AbiAlign, Align, BackendRepr, FieldsShape, HasDataLayout, Integer, LayoutData, Niche, Primitive, ReprOptions,
    Scalar, Size, StructKind, TagEncoding, TargetDataLayout, VariantLayout, Variants, WrappingRange, obj_bound,
};
use crate::rustc_index::bit_set::{ones, BitIter, BitMatrix, DenseBitSet};
use crate::rustc_index::{Idx, IdxRange, IndexSlice, IndexVec, IterEnumerated, SliceIter};
use crate::case_study::USize;
use crate::case_study::{counts, lemmas};
use crate::case_study::iter::{Filter, Map, collect_index_vec, collect_index_vec_result, iter_all, map_new_assumed};
use std::iter::{self, Enumerate};
use std::slice::IterMut;

#[derive(Clone, Debug, PartialEq)]
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

/// One more bit adds the bit at `k`: `mem` and the step of `ones` read the same bit, which is 1
/// or 0. With the base case, all `ones_assigned_disjoint` reads of the bit arithmetic.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|z: USize| z == 0 ==> ones((*s).1, z) == 0))]
#[thrust_macros::ensures(
    (DenseBitSet::<LocalIdx>::mem(*s, k) && ones((*s).1, k + 1) == ones((*s).1, k) + 1)
        || (!DenseBitSet::<LocalIdx>::mem(*s, k) && ones((*s).1, k + 1) == ones((*s).1, k)))]
#[thrust::reveal(crate::rustc_index::bit_set::ones, crate::rustc_index::bit_set::bit, crate::rustc_index::bit_set::DenseBitSet::mem)]
fn ones_step<LocalIdx: Idx + thrust_models::Model>(s: &DenseBitSet<LocalIdx>, k: usize) {}

/// The set's count is the number of its bits below its domain size.
#[thrust_macros::lemma]
#[thrust_macros::ensures(DenseBitSet::<LocalIdx>::card(*s) == ones((*s).1, (*s).0))]
#[thrust::reveal(crate::rustc_index::bit_set::DenseBitSet::card)]
fn card_ones<LocalIdx: Idx + thrust_models::Model>(s: &DenseBitSet<LocalIdx>) {}

/// An index has one value (`Idx`'s law `index_is_unique`), as a fact of `a` that
/// `split_prefix_fields`' `requires` reads at `layout()`'s tag index.
#[thrust_macros::lemma]
#[thrust_macros::requires(<I as Idx>::index_is(*a, n))]
#[thrust_macros::ensures(forall(|t: USize| <I as Idx>::index_is(*a, t) ==> t == n))]
fn index_is_only<I: Idx + thrust_models::Model>(a: &I, n: usize) {}

/// A bit iterator yields indices below its domain size, and a completed one yields nothing, in the
/// forms `Map::new` reads: the item of `next_precondition`, the second of two items of
/// `preservation_inv`, and the iterator `reinitialize` names. With a map closure that requires
/// the bound, `Map::new`'s precondition over `DenseBitSet::iter` (stage 7's promoted layouts).
/// `s` only fixes the type parameters; the facts hold of every bit iterator.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|it: <BitIter<'a, T> as thrust_models::Model>::Ty, e: <T as thrust_models::Model>::Ty, o: <BitIter<'a, T> as thrust_models::Model>::Ty|
    !<BitIter<'a, T> as crate::IteratorSpec>::produces(it, thrust_models::model::Seq::singleton(e), o)
        || <T as Idx>::index_logic(e) < it.4))]
#[thrust_macros::ensures(forall(|it: <BitIter<'a, T> as thrust_models::Model>::Ty, v: thrust_models::model::Seq<<T as thrust_models::Model>::Ty>,
        e1: <T as thrust_models::Model>::Ty, e2: <T as thrust_models::Model>::Ty, o: <BitIter<'a, T> as thrust_models::Model>::Ty|
    !<BitIter<'a, T> as crate::IteratorSpec>::produces(it, v.push(e1).push(e2), o)
        || <T as Idx>::index_logic(e2) < it.4))]
#[thrust_macros::ensures(forall(|cur: <BitIter<'a, T> as thrust_models::Model>::Ty, fin: <BitIter<'a, T> as thrust_models::Model>::Ty,
        v: thrust_models::model::Seq<<T as thrust_models::Model>::Ty>, o: <BitIter<'a, T> as thrust_models::Model>::Ty|
    !(<BitIter<'a, T> as crate::IteratorSpec>::completed(thrust_models::model::Mut::new(cur, fin))
        && <BitIter<'a, T> as crate::IteratorSpec>::produces(fin, v, o))
        || v.len() == 0))]
fn bit_iter_yields_below<'a, T: Idx + thrust_models::Model>(s: &'a DenseBitSet<T>) {}

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
// The written loop invariants (the outer loop over the variants has none;
// Thrust infers it) restate what the code after each loop needs: the lengths,
// the requirements on the arguments, and properties 1, 2 and 4 in the form
// that holds at that loop (`nb_locals` and, once dead,
// `variant_fields` are read at entry through `FnParam`). Where the live
// `variant_fields` and `storage_conflicts` are needed too, a second
// `invariant!` at the same header states the facts about them; the inner
// loop's invariants tie the two `variant_fields` together through
// `iter!('variants).0`.
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
fn coroutine_saved_local_eligibility<VariantIdx: Idx, FieldIdx: Idx, LocalIdx: Idx + thrust_models::Model<Ty: PartialEq>>(
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

    // Rewrite (rewrites.md R5): the label `'variants`, through which the inner loop's invariants
    // name this loop's iterator (`iter!('variants)`).
    'variants: for (variant_index, fields) in variant_fields.iter_enumerated() {
        for local in fields {
            // `variant_index` is the variant at `iter!('variants).1 - 1`, whose fields `iter`
            // walks; property 1 covers the variants before it and its locals before `iter.1`.
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, iter!('variants): IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, iter: SliceIter<LocalIdx>, variant_index: VariantIdx, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>, nb_locals: thrust_models::FnParam<usize>|
                assignments.len() == nb_locals.at_entry()
                && ineligible_locals.0 == nb_locals.at_entry()
                && DenseBitSet::<LocalIdx>::words_cover_domain(ineligible_locals)
                && 0 <= DenseBitSet::<LocalIdx>::card(ineligible_locals)
                && DenseBitSet::<LocalIdx>::card(ineligible_locals) <= ineligible_locals.0
                && iter!('variants).1 >= 0 && iter!('variants).1 <= iter!('variants).0.len() && *iter!('variants).0 == *variant_fields
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
                && forall(|p: USize| <VariantIdx as Idx>::index_is(variant_index, p) ==> p + 1 == iter!('variants).1)
            );
            thrust_macros::invariant!(
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, iter!('variants): IterEnumerated<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, iter: SliceIter<LocalIdx>, variant_index: VariantIdx, variant_fields: thrust_models::FnParam<&IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>>, nb_locals: thrust_models::FnParam<usize>|
                *iter!('variants).0 == *variant_fields.at_entry()
                && forall(|v: USize, f: USize| 0 <= v && v < (*variant_fields.at_entry()).len() && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> forall(|i: USize| <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], i) ==> i < nb_locals.at_entry()))
                && forall(|p: USize| <VariantIdx as Idx>::index_is(variant_index, p) ==> *iter.0 == (*variant_fields.at_entry())[p])
                && forall(|l: USize, v: USize, f: USize|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned
                        && 0 <= v && v + 1 < iter!('variants).1 && 0 <= f && f < (*variant_fields.at_entry())[v].len() ==> !<LocalIdx as Idx>::index_is((*variant_fields.at_entry())[v][f], l))
                && forall(|l: USize, k: USize|
                    0 <= l && l < nb_locals.at_entry() && assignments[l] == SavedLocalEligibility::Unassigned && 0 <= k && k < iter.1 ==> !<LocalIdx as Idx>::index_is(iter.0[k], l))
                && forall(|k: USize, v: <VariantIdx as thrust_models::Model>::Ty, i: USize|
                    0 <= k && k < assignments.len() && assignments[k] == SavedLocalEligibility::Assigned(v) && <VariantIdx as Idx>::index_is(v, i) ==> (i < (*variant_fields.at_entry()).len()
                        && exists(|f: USize| 0 <= f && f < (*variant_fields.at_entry())[i].len() && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[i][f], k))))
                && forall(|l: USize, w: USize, f: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w + 1 < iter!('variants).1 && 0 <= f && f < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w)
                && forall(|l: USize, w: USize, f: USize, g: USize, vi: <VariantIdx as thrust_models::Model>::Ty|
                    0 <= l && l < nb_locals.at_entry() && 0 <= w && w + 1 < iter!('variants).1 && 0 <= f && f < (*variant_fields.at_entry())[w].len() && 0 <= g && g < (*variant_fields.at_entry())[w].len()
                        && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][f], l) && <LocalIdx as Idx>::index_is((*variant_fields.at_entry())[w][g], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
                && forall(|l: USize, k: USize, vi: <VariantIdx as thrust_models::Model>::Ty, vn: USize|
                    0 <= l && l < nb_locals.at_entry() && 0 <= k && k < iter.1 && <LocalIdx as Idx>::index_is(iter.0[k], l)
                        && assignments[l] == SavedLocalEligibility::Assigned(vi) && <VariantIdx as Idx>::index_is(vi, vn) ==> vn + 1 == iter!('variants).1)
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

    // Rewrite (rewrites.md R5): the label `'rows`, through which the inner loop's invariant names
    // this loop's iterator (`iter!('rows)`).
    'rows: for local_a in storage_conflicts.rows() {
        // The loop only turns locals into `Ineligible(None)` members of `ineligible_locals`, so
        // properties 1, 2 and 4 carry over.
        thrust_macros::invariant!(
            |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, iter: IdxRange<LocalIdx>, storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, nb_locals: thrust_models::FnParam<usize>|
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
            && iter.start >= 0 && iter.end == (*storage_conflicts).num_rows
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
                |assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, ineligible_locals: DenseBitSet<LocalIdx>, iter: BitIter<LocalIdx>, iter!('rows): IdxRange<LocalIdx>, local_a: LocalIdx, storage_conflicts: &BitMatrix<LocalIdx, LocalIdx>, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, nb_locals: thrust_models::FnParam<usize>|
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
                && iter!('rows).start >= 0 && iter!('rows).end == (*storage_conflicts).num_rows
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
            make_ineligible(&mut ineligible_locals, &mut assignments, remove);
        }
    }

    {
        let mut used_variants = DenseBitSet::new_empty(variant_fields.len());
        for assignment in &assignments {
            // Every variant assigned so far is below `used_variants`'s domain, whose words cover it.
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
            set_assignment(&mut assignments, local, Ineligible(Some(FieldIdx::new(idx))));
        }
    }

    (ineligible_locals, assignments)
}

// Rewrite (rewrites.md R10): the two writes that make `remove` ineligible in the storage-conflict
// loop, as a function. Its inferred contract relates only its parameters, so the loop's back edge
// reads one call result instead of the results of `insert`, `deref_mut` and `index_mut`, each a
// template over every live variable.
#[thrust_macros::context]
fn make_ineligible<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model<Ty: PartialEq>>(
    ineligible_locals: &mut DenseBitSet<LocalIdx>,
    assignments: &mut IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    remove: LocalIdx,
) {
    ineligible_locals.insert(remove);
    assignments[remove] = SavedLocalEligibility::Ineligible(None);
}

// Rewrite (rewrites.md R10): the write of the last loop, as a function whose contract states
// what it does, so that the loop's back edge reads one call result instead of the results of
// `deref_mut` and `index_mut`.
#[thrust_macros::requires(forall(|i: USize| <LocalIdx as Idx>::index_is(local, i) ==> i < (*assignments).len()))]
#[thrust_macros::ensures(
    (!assignments).len() == (*assignments).len()
    && forall(|l: USize| 0 <= l && l < (*assignments).len() && <LocalIdx as Idx>::index_is(local, l)
        ==> (!assignments)[l] == value)
    && forall(|l: USize| 0 <= l && l < (*assignments).len() && !<LocalIdx as Idx>::index_is(local, l)
        ==> (!assignments)[l] == (*assignments)[l])
)]
// The fail twin of the eligibility root sets this cfg: the write leaves the other locals as they
// are, so a contract that every local gets `value` is refuted.
#[cfg_attr(thrust_eligibility_fail, thrust_macros::ensures(
    forall(|l: USize| 0 <= l && l < (*assignments).len() ==> (!assignments)[l] == value)
))]
#[thrust_macros::context]
fn set_assignment<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx>(
    assignments: &mut IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    local: LocalIdx,
    value: SavedLocalEligibility<VariantIdx, FieldIdx>,
) {
    assignments[local] = value;
}

/// Property 3 at the promoted fields: an `Ineligible` local's field index is below the lengths of
/// the promoted offsets and memory index. `combine_offsets` and its offsets closure require it. The
/// fail root layout.rs (`thrust_layout_fail`) defines it as `true`, so that the closure's `unwrap`
/// of an `Ineligible` local's field index is refuted.
#[cfg(not(thrust_layout_fail))]
#[thrust_macros::predicate]
fn ineligible_promoted<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
) -> bool {
    forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
        !(0 <= l && l < (*assignments).len() && (*assignments)[l] == SavedLocalEligibility::Ineligible(x))
        || exists(|k: <FieldIdx as thrust_models::Model>::Ty|
            x == Some(k)
                && forall(|i: USize|
                    !<FieldIdx as Idx>::index_is(k, i)
                        || (i < (*promoted_offsets).len() && i < (*promoted_memory_index).len()))))
}

#[cfg(thrust_layout_fail)]
#[thrust_macros::predicate]
fn ineligible_promoted<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
) -> bool {
    true
}

/// `m` is the number of the variant's entries Assigned to it: what `variant_field_layouts` gives of
/// its result and `combine_offsets` requires of its m. Opaque: only `combine_offsets` reads the
/// count, for the zip's pairs.
#[thrust_macros::predicate]
#[thrust::opaque]
fn assigned_count<FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model, VariantIdx: Idx + thrust_models::Model>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    index: VariantIdx,
    m: USize,
) -> bool {
    m == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
        *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), (*variant_fields).len())
}

/// `assigned_count` from the count it names.
#[thrust_macros::lemma]
#[thrust_macros::requires(m == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
    *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), (*variant_fields).len()))]
#[thrust_macros::ensures(assigned_count::<FieldIdx, LocalIdx, VariantIdx>(variant_fields, assignments, index, m))]
#[thrust::reveal(assigned_count)]
fn assigned_count_of<FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model, VariantIdx: Idx + thrust_models::Model>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    index: VariantIdx,
    m: usize,
) {}

/// The variant's entries Assigned to it among the first `k` are at most those among the first `n`,
/// for every `k <= n`, by induction over `n`.
#[thrust_macros::lemma]
#[thrust_macros::variant(n)]
#[thrust_macros::ensures(forall(|k: USize| 0 <= k && k <= n
    ==> counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
            *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), k)
        <= counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
            *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), n)))]
fn assigned_cnt_le<FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model, VariantIdx: Idx + thrust_models::Model>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    index: VariantIdx,
    n: usize,
) {
    if n > 0 {
        assigned_cnt_le(variant_fields, assignments, index, n - 1);
    }
}

/// At an entry Assigned to the variant, the count before the next position is one more than the
/// count before the entry, and at most the count of all the `n` entries.
#[thrust_macros::lemma]
#[thrust_macros::requires(n == (*variant_fields).len()
    && <FieldIdx as Idx>::index_logic(i) < (*variant_fields).len()
    && (*assignments)[<LocalIdx as Idx>::index_logic((*variant_fields)[<FieldIdx as Idx>::index_logic(i)])]
        == SavedLocalEligibility::Assigned(index))]
#[thrust_macros::ensures(counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
        *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), <FieldIdx as Idx>::index_logic(i) + 1)
        == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
            *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), <FieldIdx as Idx>::index_logic(i)) + 1
    && counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
        *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), <FieldIdx as Idx>::index_logic(i) + 1)
        <= counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
            *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), (*variant_fields).len()))]
fn assigned_entry_counted<FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model, VariantIdx: Idx + thrust_models::Model>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    index: VariantIdx,
    i: FieldIdx,
    n: usize,
) {
    assigned_cnt_le(variant_fields, assignments, index, n);
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
        && assigned_count::<FieldIdx, LocalIdx, VariantIdx>(variant_fields, assignments, index, result.len())
        && counts::selection_of::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>, F>(
            &result, *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), local_layouts)
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
            // The bound is the `requires`', restated for `Map::yields_entries_of`.
            ensures(<LocalIdx as Idx>::index_logic(*local) < (**local_layouts).len()
                && result == (**local_layouts)[<LocalIdx as Idx>::index_logic(*local)]),
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

    // The fields collected below are exactly the entries Assigned to the variant: the filter
    // accepts those, and `collect` runs the map to its end. The lemma's proof is open: its
    // `ensures`, the body of `filter_selects_all` and the count at `collect`'s witness below get
    // no answer from the solver.
    thrust_macros::proof!(counts::map_count_exact(
        &variant_only_tys,
        variant_fields,
        &assignments,
        &Assigned(index),
        variant_fields.len(),
    ));

    // The fields collected below are, in order, the layouts of a selection of the entries Assigned
    // to the variant, which `variant_layout` reads `variant_fits_wf` at: the filter accepts those
    // entries, and the map closure returns the layout of the local it is given.
    thrust_macros::proof!(counts::map_selected_entries(
        &variant_only_tys,
        variant_fields,
        &assignments,
        &Assigned(index),
        local_layouts,
    ));
    // Each field collected is an entry of `local_layouts`: the map closure's `ensures`.
    thrust_macros::proof!(Map::yields_entries_of(&variant_only_tys, local_layouts));
    // Rewrite (rewrites.md R8): `collect_index_vec` for `collect`; the result is bound to a name,
    // for the `assume!`. Its precondition, the map's `inv`, is `Map::new`'s `ensures`.
    let fields = collect_index_vec(variant_only_tys);
    // The fields are as many as the variant's entries Assigned to it, which `combine_offsets`
    // requires: `map_count_exact` at `collect`'s witness. Assumed (fallback): the solver does not
    // answer this cut; delete the `assume!` for the `proof_assert!` once it does.
    thrust_macros::assume!(
        |fields: IndexVec<FieldIdx, F>, variant_fields: &IndexVec<FieldIdx, LocalIdx>,
            assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, index: VariantIdx|
            fields.len() == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), (*variant_fields).len())
    );
    // Reachability twin of the fallback's assumptions in this function (fail root
    // layout_reach_fallback.rs).
    #[cfg(thrust_layout_reach_fallback)]
    thrust_macros::proof_assert!(|| false);
    thrust_macros::proof!(assigned_count_of(variant_fields, &assignments, index, fields.len()));
    // The `ensures`' selection, at `collect`'s witness.
    thrust_macros::proof_assert!(
        |fields: IndexVec<FieldIdx, F>, variant_fields: &IndexVec<FieldIdx, LocalIdx>, local_layouts: &IndexSlice<LocalIdx, F>,
            assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, index: VariantIdx|
            counts::selection_of::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>, F>(
                &fields, *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), local_layouts)
    );
    // The `ensures`' count and entries, one `proof_assert!` each, before the return.
    thrust_macros::proof_assert!(
        |fields: IndexVec<FieldIdx, F>, assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, index: VariantIdx|
            fields.len()
                <= counts::class_cnt::<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                    *assignments, (*assignments).len(), SavedLocalEligibility::Assigned(index))
    );
    thrust_macros::proof_assert!(|fields: IndexVec<FieldIdx, F>, local_layouts: &IndexSlice<LocalIdx, F>|
        forall(|k: USize|
            !(0 <= k && k < fields.len())
            || exists(|i: USize| 0 <= i && i < (*local_layouts).len() && fields[k] == (*local_layouts)[i]))
    );
    fields
}

/// What `combine_offsets` reads of the variant's entries and the promoted fields, which do not
/// depend on its m: `FieldIdx` reaching the entries' number, the promoted memory index's entries
/// below its length, every entry a local below n that is not `Unassigned` (property 1), and
/// property 3 (`ineligible_promoted`). Opaque: `variant_layout` states it at its start, where its
/// `requires` gives it, and passes it to the call as one atom.
#[thrust_macros::predicate]
#[thrust::opaque]
fn combine_wf<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
) -> bool {
    forall(|k: USize| !(0 <= k && k <= (*variant_fields).len()) || <FieldIdx as Idx>::can_new(k))
        && forall(|k: USize, i: USize|
            !(0 <= k && k < (*promoted_memory_index).len() && <u32 as Idx>::index_is((*promoted_memory_index)[k], i))
                || i < (*promoted_memory_index).len())
        && forall(|f: usize, i: USize|
            !(0 <= f && f < (*variant_fields).len() && <LocalIdx as Idx>::index_is((*variant_fields)[f], i))
                || (i < (*assignments).len() && (*assignments)[i] != SavedLocalEligibility::Unassigned))
        && ineligible_promoted::<VariantIdx, FieldIdx, LocalIdx>(assignments, promoted_offsets, promoted_memory_index)
}

/// `combine_wf` from its facts in the forms `variant_layout`'s `requires` gives.
#[thrust_macros::lemma]
#[thrust_macros::requires(
    forall(|k: USize| 0 <= k && k <= (*variant_fields).len() ==> <FieldIdx as Idx>::can_new(k))
        && forall(|k: USize, i: USize|
            0 <= k && k < (*promoted_memory_index).len() && <u32 as Idx>::index_is((*promoted_memory_index)[k], i)
                ==> i < (*promoted_memory_index).len())
        && forall(|f: usize, i: USize|
            0 <= f && f < (*variant_fields).len() && <LocalIdx as Idx>::index_is((*variant_fields)[f], i)
                ==> (i < (*assignments).len() && (*assignments)[i] != SavedLocalEligibility::Unassigned))
        && ineligible_promoted::<VariantIdx, FieldIdx, LocalIdx>(assignments, promoted_offsets, promoted_memory_index)
)]
#[thrust_macros::ensures(combine_wf::<VariantIdx, FieldIdx, LocalIdx>(variant_fields, assignments, promoted_offsets, promoted_memory_index))]
#[thrust::reveal(combine_wf)]
fn combine_wf_of<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
) {}

// Rewrite (rewrites.md R12): the part of `layout()`'s per-variant closure that destructures the
// variant's fields and combines its offsets and memory order with the promoted ones, as a function
// whose `requires` states what the code reads: the fields are `Arbitrary` with m offsets and a
// memory order that is a permutation of `0..m` (univariant's `arbitrary_of`), `FieldIdx` and `u32` reach c + m (c the promoted fields), every
// entry of the variant is a local below n that is not `Unassigned` (property 1), and an
// `Ineligible` local's field index is below c (property 3), and m is the number of the variant's
// entries Assigned to it, which the zip's pairs are taken at. Its `ensures` is `true`: `layout()`
// states nothing of the variants it returns.
#[thrust_macros::requires(
    FieldsShape::<FieldIdx>::arbitrary_of(fields, m)
        && assigned_count::<FieldIdx, LocalIdx, VariantIdx>(variant_fields, assignments, index, m)
        && forall(|k: USize| 0 <= k && k <= m ==> <u32 as Idx>::can_new(k))
        && forall(|k: USize| 0 <= k && k <= (*promoted_memory_index).len() + m ==> <FieldIdx as Idx>::can_new(k))
        && (*promoted_memory_index).len() + m <= 4294967295usize
        && combine_wf::<VariantIdx, FieldIdx, LocalIdx>(variant_fields, assignments, promoted_offsets, promoted_memory_index)
        && forall(|f: usize, v: <VariantIdx as thrust_models::Model>::Ty|
            !(0 <= f && f < (*variant_fields).len()
                && (*assignments)[<LocalIdx as Idx>::index_logic((*variant_fields)[f])] == SavedLocalEligibility::Assigned(v))
            || v == index)
)]
#[thrust_macros::ensures(true)]
#[thrust_macros::context]
#[thrust::reveal(super::super::FieldsShape::arbitrary_of, combine_wf, assigned_count)]
fn combine_offsets<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    index: VariantIdx,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
    fields: FieldsShape<FieldIdx>,
    m: usize,
) -> (IndexVec<FieldIdx, Size>, IndexVec<u32, FieldIdx>) {
    use SavedLocalEligibility::*;

    let FieldsShape::Arbitrary {
        offsets,
        in_memory_order,
    } = fields
    else {
        // Unreachable by `arbitrary_of`.
        unreachable!();
    };

    // `invert_bijective_mapping` needs `u32::can_new` up to the number of fields m, and
    // `FieldIdx::new(invalid_field_idx)` needs `FieldIdx::can_new(c + m)`: c + m <= n by
    // `filter_count` above and the closure's `requires` on c.
    let memory_index = in_memory_order.invert_bijective_mapping();
    let invalid_field_idx = promoted_memory_index.len() + memory_index.len();
    let mut combined_in_memory_order =
        IndexVec::from_elem_n(FieldIdx::new(invalid_field_idx), invalid_field_idx);

    let mut offsets_and_memory_index = iter::zip(offsets, memory_index);
    // The closure's `requires` of the zip at the first entry: both parts at 0, the count of the
    // entries before it, of m pairs (`arbitrary_of` and `invert_bijective_mapping`), m the count
    // of all the variant's entries Assigned to it (`assigned_count`), memory indices below m.
    thrust_macros::proof_assert!(|offsets_and_memory_index: std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>>, variant_fields: &IndexVec<FieldIdx, LocalIdx>,
            assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, index: VariantIdx|
        offsets_and_memory_index.0.1 == 0
            && offsets_and_memory_index.1.1 == 0
            && offsets_and_memory_index.0.0.len() == offsets_and_memory_index.1.0.len()
            && offsets_and_memory_index.0.0.len() == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), (*variant_fields).len()));
    thrust_macros::proof_assert!(|offsets_and_memory_index: std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>>, invalid_field_idx: usize, promoted_memory_index: &IndexVec<FieldIdx, u32>|
        forall(|k: USize|
            0 <= k && k < offsets_and_memory_index.1.0.len()
                ==> offsets_and_memory_index.1.0[k] < offsets_and_memory_index.1.0.len())
            && invalid_field_idx == (*promoted_memory_index).len() + offsets_and_memory_index.1.0.len());
    // Rewrite (rewrites.md R8): `Map::new` and `collect_index_vec` for `map` and `collect`.
    // The closure's contract: its `requires` states what its body reads, of the entry it is given
    // (a local below n that is not `Unassigned`, Assigned to this variant if at all: property 2b)
    // and of its captures (property 3, the promoted memory index below c,
    // `combined_in_memory_order`'s length c + m, and the zip's `inv`, which `next` requires), and
    // ties the zip to the entry's position p: its two parts are at one position, the count of the
    // entries Assigned to the variant before p, of m (the count of all of them) pairs, whose memory
    // indices are below m. Its `ensures` moves the zip to the count before p + 1, as the entry's
    // class decides whether the body takes a pair. Its `hist_inv` keeps what the `requires` reads
    // of the captures across calls: the shared captures are unchanged and the writes to
    // `combined_in_memory_order` keep its length. `Map::new`'s `next_precondition` follows from
    // `combine_offsets`' `requires` on the variant's entries, with the zip at 0 and
    // `assigned_count`'s m, and its `preservation_inv` from the `ensures` at the next position.
    // Rewrite (rewrites.md R13): the entries' iterator is bound to a name, for `yields_last`: the
    // entry and position of the next item, which `Map::new`'s `preservation_inv` reads.
    let entries = variant_fields.iter_enumerated();
    thrust_macros::proof!(IterEnumerated::yields_last(&entries));
    let combined_offsets = collect_index_vec(Map::new(
        entries,
        thrust_macros::closure!(
        captures(
            assignments: &mut &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
            offsets_and_memory_index: &mut &mut std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>>,
            promoted_memory_index: &mut &IndexVec<FieldIdx, u32>,
            invalid_field_idx: &mut &usize,
            promoted_offsets: &mut &IndexVec<FieldIdx, Size>,
            combined_in_memory_order: &mut &mut IndexVec<u32, FieldIdx>,
            variant_fields: &mut &IndexVec<FieldIdx, LocalIdx>,
            index: &mut &VariantIdx,
        ),
        requires(
            <LocalIdx as Idx>::index_logic(*local) < (**assignments).len()
                && (**assignments)[<LocalIdx as Idx>::index_logic(*local)] != SavedLocalEligibility::Unassigned
                && ineligible_promoted::<VariantIdx, FieldIdx, LocalIdx>(*assignments, *promoted_offsets, *promoted_memory_index)
                && forall(|k: USize, i: USize|
                    !(0 <= k && k < (**promoted_memory_index).len() && <u32 as Idx>::index_is((**promoted_memory_index)[k], i))
                    || i < (**promoted_memory_index).len())
                && (**promoted_memory_index).len() <= **invalid_field_idx
                && **invalid_field_idx <= 4294967295usize
                && (**combined_in_memory_order).len() == **invalid_field_idx
                && <std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>> as crate::IteratorSpec>::inv(**offsets_and_memory_index)
                && forall(|v: <VariantIdx as thrust_models::Model>::Ty|
                    !((**assignments)[<LocalIdx as Idx>::index_logic(*local)] == SavedLocalEligibility::Assigned(v))
                    || v == **index)
                && <FieldIdx as Idx>::index_logic(i) < (**variant_fields).len()
                && *local == (**variant_fields)[<FieldIdx as Idx>::index_logic(i)]
                && (**offsets_and_memory_index).0.1 == (**offsets_and_memory_index).1.1
                && (**offsets_and_memory_index).0.0.len() == (**offsets_and_memory_index).1.0.len()
                && (**offsets_and_memory_index).0.1 == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                    **variant_fields, **assignments, SavedLocalEligibility::Assigned(**index), <FieldIdx as Idx>::index_logic(i))
                && (**offsets_and_memory_index).0.0.len() == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                    **variant_fields, **assignments, SavedLocalEligibility::Assigned(**index), (**variant_fields).len())
                && forall(|k: USize|
                    !(0 <= k && k < (**offsets_and_memory_index).1.0.len())
                    || (**offsets_and_memory_index).1.0[k] < (**offsets_and_memory_index).1.0.len())
                && **invalid_field_idx == (**promoted_memory_index).len() + (**offsets_and_memory_index).1.0.len()
        ),
        ensures(
            (*!offsets_and_memory_index).0.0 == (**offsets_and_memory_index).0.0
                && (*!offsets_and_memory_index).1.0 == (**offsets_and_memory_index).1.0
                && (*!offsets_and_memory_index).0.1 == (*!offsets_and_memory_index).1.1
                && (*!offsets_and_memory_index).0.0.len() == (*!offsets_and_memory_index).1.0.len()
                && (*!offsets_and_memory_index).0.0.len() == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                    **variant_fields, **assignments, SavedLocalEligibility::Assigned(**index), (**variant_fields).len())
                && forall(|k: USize|
                    !(0 <= k && k < (*!offsets_and_memory_index).1.0.len())
                    || (*!offsets_and_memory_index).1.0[k] < (*!offsets_and_memory_index).1.0.len())
                && **invalid_field_idx == (**promoted_memory_index).len() + (*!offsets_and_memory_index).1.0.len()
                && <std::iter::Zip<std::vec::IntoIter<Size>, std::vec::IntoIter<u32>> as crate::IteratorSpec>::inv(*!offsets_and_memory_index)
                && (*!offsets_and_memory_index).0.1 == counts::acc_cnt::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                    **variant_fields, **assignments, SavedLocalEligibility::Assigned(**index), <FieldIdx as Idx>::index_logic(i) + 1)
        ),
        hist_inv(
            *assignments == !assignments
                && *variant_fields == !variant_fields
                && *index == !index
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
                    // The entry is Assigned to this variant (property 2b), so the count before
                    // p + 1 is the zip's position plus one, at most m.
                    thrust_macros::proof!(assigned_entry_counted(variant_fields, assignments, index, i, variant_fields.len()));
                    // Rewrite (rewrites.md R12): the pair, c and c + m are bound to names, for the
                    // `proof_assert!`, which names local variables only (not a closure's captures).
                    let pair = offsets_and_memory_index.next();
                    let promoted_count = promoted_memory_index.len();
                    let bound = invalid_field_idx;
                    // `next` returns a pair, as the zip's position is below m, and its memory
                    // index j has c + j < c + m = `invalid_field_idx` (the `requires`). With it,
                    // the `u32` sum stays below c + m <= u32::MAX and indexes
                    // `combined_in_memory_order`.
                    thrust_macros::proof_assert!(
                        |pair: Option<(Size, u32)>, promoted_count: usize, bound: usize|
                            exists(|o: Size, j: <u32 as thrust_models::Model>::Ty| pair == Some((o, j)) && promoted_count + j < bound)
                    );
                    // Reachability twin (fail root layout_reach_pair.rs): the path after the
                    // `proof_assert!` is reachable, so the closure's `requires` makes no proof here
                    // vacuous.
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
            // `invalid_field_idx` by the `proof_assert!` above, an Ineligible local's is an entry of
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
        && n <= 4294967295usize
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
    // the count of the split; and the items taken are at most n <= u32::MAX, so the two lengths
    // stay within `u32`'s bound, which `IndexVec::push` requires (the parts are indexed by `u32`).
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
                    && produced.len() <= n
                    && n <= 4294967295usize
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


// Rewrite (rewrites.md R15): the steps of `layout()` that append the tag's layout and the promoted
// locals' layouts to the prefix's fields (`push`, and `extend` by the map of the ineligible set),
// as a function whose contract states what `layout()` reads of them: P + 1 + c fields, c the set's
// count (at least 0, which the tag's index below the length needs), the entry fields kept, the tag's layout at P, the fields after it layouts of
// `local_layouts`, `FieldIdx` reaching the new length, and `layout_wf` of every field.
#[thrust_macros::requires(
    forall(|k: USize|
        0 <= k && k <= (*prefix_layouts).len() + 1 + (*local_layouts).len() ==> <FieldIdx as Idx>::can_new(k))
        && (*ineligible_locals).0 == (*local_layouts).len()
        // `LocalIdx` reaches every local: the set's iterator's `inv`, which `Map::new` and
        // `extend_from` require.
        && forall(|k: USize| 0 <= k && k < (*local_layouts).len() ==> <LocalIdx as Idx>::can_new(k))
        && layouts_wf::<FieldIdx, F, FieldIdx, VariantIdx, C>(*calc, &*prefix_layouts)
        && layouts_wf::<LocalIdx, F, FieldIdx, VariantIdx, C>(*calc, local_layouts)
        && layout_wf::<F, FieldIdx, VariantIdx, C>(*calc, tag_layout)
)]
#[thrust_macros::ensures(
    (!prefix_layouts).len() == (*prefix_layouts).len() + 1 + DenseBitSet::<LocalIdx>::card(*ineligible_locals)
        && 0 <= DenseBitSet::<LocalIdx>::card(*ineligible_locals)
        && DenseBitSet::<LocalIdx>::card(*ineligible_locals) <= (*local_layouts).len()
        && forall(|k: USize| !(0 <= k && k < (*prefix_layouts).len()) || (!prefix_layouts)[k] == (*prefix_layouts)[k])
        && (!prefix_layouts)[(*prefix_layouts).len()] == tag_layout
        && forall(|k: USize|
            !((*prefix_layouts).len() < k && k < (!prefix_layouts).len())
                || exists(|i: USize| 0 <= i && i < (*local_layouts).len() && (!prefix_layouts)[k] == (*local_layouts)[i]))
)]
#[thrust_macros::ensures(forall(|k: USize| !(0 <= k && k <= (!prefix_layouts).len()) || <FieldIdx as Idx>::can_new(k)))]
#[thrust_macros::ensures(layouts_wf::<FieldIdx, F, FieldIdx, VariantIdx, C>(*calc, &!prefix_layouts))]
#[thrust_macros::context]
#[thrust::reveal(layouts_wf)]
fn promote_locals<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    LocalIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: &LayoutCalculator<C>,
    prefix_layouts: &mut IndexVec<FieldIdx, F>,
    tag_layout: F,
    ineligible_locals: &DenseBitSet<LocalIdx>,
    local_layouts: &IndexSlice<LocalIdx, F>,
) {
    // Rewrite (rewrites.md R8): `Map::new(it, f)` for `it.map(f)`, `extend_from` for `extend`.
    // The closure's contract, as that of the per-variant closure's map closure in `layout()`: a
    // member of the set is a local below n, and the closure returns its layout. `Map::new`'s
    // precondition reads the members through `bit_iter_yields_below`.
    thrust_macros::proof!(bit_iter_yields_below(ineligible_locals));
    let promoted_layouts = Map::new(
        ineligible_locals.iter(),
        thrust_macros::closure!(
            captures(local_layouts: &mut &IndexSlice<LocalIdx, F>),
            requires(<LocalIdx as Idx>::index_logic(local) < (**local_layouts).len()),
            // The bound is the `requires`', restated for `Map::yields_entries_of`.
            ensures(<LocalIdx as Idx>::index_logic(local) < (**local_layouts).len()
                && result == (**local_layouts)[<LocalIdx as Idx>::index_logic(local)]),
            |local: LocalIdx| -> F { local_layouts[local] },
        ),
    );
    // The promoted layouts are entries of `local_layouts`.
    thrust_macros::proof!(Map::yields_entries_of(&promoted_layouts, local_layouts));
    // `push` and `extend_from` give P + 1 + c fields, c the items `ineligible_locals.iter()` yields
    // (`Map` keeps the length), which is the set's count `card`: `iter` starts `BitIter`'s `left`
    // at it, and the iterator completes with nothing left. The fields after the tag are layouts of
    // `local_layouts` (the closure's `ensures`).
    prefix_layouts.push(tag_layout);
    prefix_layouts.extend_from(promoted_layouts);
}

// Rewrite (rewrites.md R16): the `match` of `layout()` on the prefix's fields, which splits the
// offsets and the memory order at the promoted fields (b_start = P + 1, P the tag's index), as a
// function whose contract states what `layout()` reads of the parts: the promoted offsets and
// memory index have n - (P + 1) = c entries, and each entry of the memory index is below c
// (`invert_bijective_mapping`), which `combine_offsets` requires. `u32` reaches n, for
// `invert_bijective_mapping`.
#[thrust_macros::requires(
    FieldsShape::<FieldIdx>::arbitrary_of(fields, n)
        && forall(|t: USize| <FieldIdx as Idx>::index_is(tag_index, t) ==> t + 1 <= n)
        && forall(|k: USize| 0 <= k && k <= n ==> <FieldIdx as Idx>::can_new(k))
        && n <= 4294967295usize
)]
#[thrust_macros::ensures(forall(|t: USize|
    !<FieldIdx as Idx>::index_is(tag_index, t) || (result.1.len() + t + 1 == n && result.2.len() + t + 1 == n)))]
#[thrust_macros::ensures(forall(|k: USize, i: USize|
    !(0 <= k && k < result.2.len() && <u32 as Idx>::index_is(result.2[k], i)) || i < result.2.len()))]
#[thrust_macros::context]
#[thrust::reveal(super::super::FieldsShape::arbitrary_of)]
fn split_prefix_fields<FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>>(
    fields: FieldsShape<FieldIdx>,
    tag_index: FieldIdx,
    n: usize,
) -> (FieldsShape<FieldIdx>, IndexVec<FieldIdx, Size>, IndexVec<FieldIdx, u32>) {
    match fields {
        FieldsShape::Arbitrary {
            mut offsets,
            in_memory_order,
        } => {
            let b_start = tag_index.plus(1);
            // `split_off(b_start.index())` needs `b_start.index() <= offsets.raw.len()`: `b_start`
            // is P + 1 (`plus`), and `offsets` has n entries (`arbitrary_of`).
            let offsets_b = IndexVec::from_raw(offsets.raw.split_off(b_start.index()));
            let offsets_a = offsets;

            // Rewrite (rewrites.md R11): the loop that splits the memory order at `b_start` is
            // `split_in_memory_order`. Its `requires` holds by `arbitrary_of` (the order is a
            // permutation of `0..n`) and the `requires` (`FieldIdx` reaches n); its `ensures`
            // gives the second part n - (P + 1) = c entries, each below c:
            // `invert_bijective_mapping` needs its entries below its length, and the variants need
            // `promoted_memory_index` to have c entries.
            let (in_memory_order_a, in_memory_order_b) =
                split_in_memory_order(in_memory_order, b_start, n);

            let outer_fields = FieldsShape::Arbitrary {
                offsets: offsets_a,
                in_memory_order: in_memory_order_a,
            };
            (
                outer_fields,
                offsets_b,
                // `invert_bijective_mapping` requires every element of `in_memory_order_b` below
                // its length, and keeps the length.
                in_memory_order_b.invert_bijective_mapping(),
            )
        }
        // Unreachable by `arbitrary_of`.
        _ => unreachable!(),
    }
}

/// What `layout()` requires of a layout it passes to `univariant`: its largest niche is well formed
/// in the data layout `calc` names and lies within the layout, a scalar `backend_repr` is well
/// formed and its size below the object size bound
/// (`univariant`'s `layout_pre`, of one field).
#[thrust_macros::predicate]
#[thrust::opaque]
fn layout_wf<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: LayoutCalculator<C>,
    x: F,
) -> bool {
    forall(|dl: TargetDataLayout, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
            !(C::dl_of(calc, dl)
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&x), d) && **d == l
                && l.largest_niche == Some(n))
                || Niche::wf_in(n, dl))
        && forall(|dl: TargetDataLayout, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, z: Size|
            !(C::dl_of(calc, dl)
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&x), d) && **d == l
                && l.largest_niche == Some(n)
                && Primitive::size_in(n.value, dl, z))
                || n.offset.raw + z.raw <= l.size.raw)
        && forall(|dl: TargetDataLayout, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, c: Scalar|
            !(C::dl_of(calc, dl)
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&x), d) && **d == l
                && l.backend_repr == BackendRepr::Scalar(c))
                || Scalar::wf_in(c, dl))
        && forall(|dl: TargetDataLayout, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>|
            !(C::dl_of(calc, dl)
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&x), d) && **d == l)
                || l.size.raw < obj_bound(dl))
}

/// `layout_wf` of every layout of `layouts`.
#[thrust_macros::predicate]
#[thrust::opaque]
fn layouts_wf<
    'a,
    I: Idx + thrust_models::Model,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: LayoutCalculator<C>,
    layouts: &IndexSlice<I, F>,
) -> bool {
    forall(|i: USize| !(0 <= i && i < (*layouts).len()) || layout_wf::<F, FieldIdx, VariantIdx, C>(calc, (*layouts)[i]))
}

/// `layouts_wf` of fields that are entries of `local_layouts`, and `FieldIdx` reaching their
/// number: the per-variant closure's fields.
#[thrust_macros::lemma]
#[thrust_macros::requires(
    layouts_wf::<LocalIdx, F, FieldIdx, VariantIdx, C>(*calc, local_layouts)
        && forall(|k: USize|
            !(0 <= k && k < (*fields).len())
            || exists(|i: USize| 0 <= i && i < (*local_layouts).len() && (*fields)[k] == (*local_layouts)[i]))
        && (*fields).len() <= (*local_layouts).len()
        && forall(|k: USize| !(0 <= k && k <= (*local_layouts).len()) || <FieldIdx as Idx>::can_new(k))
)]
#[thrust_macros::ensures(layouts_wf::<FieldIdx, F, FieldIdx, VariantIdx, C>(*calc, fields))]
#[thrust_macros::ensures(forall(|k: USize| !(0 <= k && k <= (*fields).len()) || <FieldIdx as Idx>::can_new(k)))]
#[thrust::reveal(layouts_wf)]
fn layouts_wf_of_entries<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    LocalIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: &LayoutCalculator<C>,
    local_layouts: &IndexSlice<LocalIdx, F>,
    fields: &IndexVec<FieldIdx, F>,
) {}

/// `univariant`'s `layout_pre` of fields that are `layouts_wf`, at both `univariant` calls of
/// `layout()`. `layout_pre` is opaque in `layout()`, so the calls read it as this lemma's
/// `ensures`.
#[thrust_macros::lemma]
#[thrust_macros::requires(
    layouts_wf::<FieldIdx, F, FieldIdx, VariantIdx, C>(*calc, fields)
        && forall(|k: USize| !(0 <= k && k <= (*fields).len()) || <FieldIdx as Idx>::can_new(k))
        && (!matches!(kind, StructKind::MaybeUnsized) || (*fields).len() > 0)
        && forall(|z: USize| !(z == 0usize) || <VariantIdx as Idx>::can_new(z))
        && forall(|dl: TargetDataLayout| !C::dl_of(*calc, dl)
            || dl.default_address_space_pointer_spec.pointer_size.raw == 2
            || dl.default_address_space_pointer_spec.pointer_size.raw == 4
            || dl.default_address_space_pointer_spec.pointer_size.raw == 8)
        && forall(|dl: TargetDataLayout, ps: Size, pa: Align|
            !(C::dl_of(*calc, dl) && kind == StructKind::Prefixed(ps, pa))
                || ps.raw < obj_bound(dl))
)]
#[thrust_macros::ensures(LayoutCalculator::<C>::layout_pre::<FieldIdx, VariantIdx, F>(*calc, fields, kind))]
#[thrust_macros::context]
#[thrust::reveal(super::LayoutCalculator::layout_pre, layouts_wf, layout_wf)]
fn layout_pre_of_wf<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: &LayoutCalculator<C>,
    fields: &IndexVec<FieldIdx, F>,
    kind: StructKind,
) {
    // `layout_pre`'s conjuncts over `fields`, one step each.
    thrust_macros::proof_assert!(|calc: &LayoutCalculator<C>, fields: &IndexVec<FieldIdx, F>|
        forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche|
            !(C::dl_of(*calc, dl)
                && 0 <= i
                && i < (*fields).len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l
                && l.largest_niche == Some(n))
                || Niche::wf_in(n, dl)));
    thrust_macros::proof_assert!(|calc: &LayoutCalculator<C>, fields: &IndexVec<FieldIdx, F>|
        forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, n: Niche, z: Size|
            !(C::dl_of(*calc, dl)
                && 0 <= i
                && i < (*fields).len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l
                && l.largest_niche == Some(n)
                && Primitive::size_in(n.value, dl, z))
                || n.offset.raw + z.raw <= l.size.raw));
    thrust_macros::proof_assert!(|calc: &LayoutCalculator<C>, fields: &IndexVec<FieldIdx, F>|
        forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>, c: Scalar|
            !(C::dl_of(*calc, dl)
                && 0 <= i
                && i < (*fields).len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l
                && l.backend_repr == BackendRepr::Scalar(c))
                || Scalar::wf_in(c, dl)));
    thrust_macros::proof_assert!(|calc: &LayoutCalculator<C>, fields: &IndexVec<FieldIdx, F>|
        forall(|dl: TargetDataLayout, i: usize, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>|
            !(C::dl_of(*calc, dl)
                && 0 <= i
                && i < (*fields).len()
                && thrust_macros::post!(<F as core::ops::Deref>::deref(&(*fields)[i]), d) && **d == l)
                || l.size.raw < obj_bound(dl)));
}

/// What `variant_layout` reads of `calc`, `local_layouts` and `assignments`: their lengths,
/// `FieldIdx` and `u32` reaching n, and the conjuncts of `layout()`'s `requires` that `univariant`
/// needs. Opaque, as the other two atoms of the per-variant closure's `requires`: the closure's
/// `requires` and `Map::new`'s precondition read each as one atom, which a lemma establishes
/// where `layout()` has its facts and `variant_layout` reveals.
#[thrust_macros::predicate]
#[thrust::opaque]
fn variant_env_wf<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    LocalIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: LayoutCalculator<C>,
    local_layouts: &IndexSlice<LocalIdx, F>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
) -> bool {
    (*assignments).len() == (*local_layouts).len()
        && forall(|k: USize| !(0 <= k && k <= (*local_layouts).len()) || <FieldIdx as Idx>::can_new(k))
        && (*local_layouts).len() <= 4294967295usize
        && LayoutCalculator::<C>::deref_functional::<FieldIdx, VariantIdx, F>()
        && forall(|z: USize| !(z == 0usize) || <VariantIdx as Idx>::can_new(z))
        && forall(|dl: TargetDataLayout| !C::dl_of(calc, dl)
            || dl.default_address_space_pointer_spec.pointer_size.raw == 2
            || dl.default_address_space_pointer_spec.pointer_size.raw == 4
            || dl.default_address_space_pointer_spec.pointer_size.raw == 8)
        && layouts_wf::<LocalIdx, F, FieldIdx, VariantIdx, C>(calc, local_layouts)
}

/// What `variant_layout` reads of the variant it is given: `FieldIdx` reaching its length, its
/// entries locals below n, and stage 5's properties 1, 2b and 2c at its entries.
#[thrust_macros::predicate]
#[thrust::opaque]
fn variant_entries_wf<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    LocalIdx: Idx + thrust_models::Model,
>(
    local_layouts: &IndexSlice<LocalIdx, F>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    index: VariantIdx,
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
) -> bool {
    forall(|k: USize| !(0 <= k && k <= (*variant_fields).len()) || <FieldIdx as Idx>::can_new(k))
        && forall(|f: usize|
            !(0 <= f && f < (*variant_fields).len())
            || forall(|i: USize|
                !<LocalIdx as Idx>::index_is((*variant_fields)[f], i) || i < (*local_layouts).len()))
        // Property 1 at the variant's entries.
        && forall(|l: usize, f: usize|
            !(0 <= l && l < (*assignments).len()
                && 0 <= f && f < (*variant_fields).len()
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i)))
            || (*assignments)[l] != SavedLocalEligibility::Unassigned)
        // Property 2b: a local the variant lists is Assigned to the variant, if at all.
        && forall(|l: usize, f: usize, vi: <VariantIdx as thrust_models::Model>::Ty, w: USize|
            !(0 <= l && l < (*assignments).len()
                && 0 <= f && f < (*variant_fields).len()
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i))
                && (*assignments)[l] == SavedLocalEligibility::Assigned(vi)
                && <VariantIdx as Idx>::index_is(index, w))
            || forall(|vn: USize| !<VariantIdx as Idx>::index_is(vi, vn) || vn == w))
        // Property 2c: an Assigned local appears once in the variant's entries.
        && forall(|l: usize, f: usize, g: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
            !(0 <= l && l < (*assignments).len()
                && 0 <= f && f < (*variant_fields).len()
                && 0 <= g && g < (*variant_fields).len()
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[f], i))
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[g], i))
                && (*assignments)[l] == SavedLocalEligibility::Assigned(vi))
            || f == g)
}

/// What `variant_layout` reads of the promoted fields: property 3 at them, the promoted memory
/// index's entries below its length c, and the count c + (locals Assigned to the variant) <= n
/// that sites 1 and 3 need.
#[thrust_macros::predicate]
#[thrust::opaque]
fn variant_promoted_wf<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
    index: VariantIdx,
) -> bool {
    ineligible_promoted::<VariantIdx, FieldIdx, LocalIdx>(assignments, promoted_offsets, promoted_memory_index)
        && forall(|k: USize, i: USize|
            !(0 <= k && k < (*promoted_memory_index).len() && <u32 as Idx>::index_is((*promoted_memory_index)[k], i))
                || i < (*promoted_memory_index).len())
        && (*promoted_memory_index).len()
            + counts::class_cnt::<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                *assignments, (*assignments).len(), SavedLocalEligibility::Assigned(index))
            <= (*assignments).len()
}

/// `variant_env_wf` from `layout()`'s `requires` and eligibility's length.
#[thrust_macros::lemma]
#[thrust_macros::requires(
    (*assignments).len() == (*local_layouts).len()
        && forall(|k: USize| !(0 <= k && k <= (*local_layouts).len()) || <FieldIdx as Idx>::can_new(k))
        && (*local_layouts).len() <= 4294967295usize
        && LayoutCalculator::<C>::deref_functional::<FieldIdx, VariantIdx, F>()
        && forall(|z: USize| !(z == 0usize) || <VariantIdx as Idx>::can_new(z))
        && forall(|dl: TargetDataLayout| !C::dl_of(*calc, dl)
            || dl.default_address_space_pointer_spec.pointer_size.raw == 2
            || dl.default_address_space_pointer_spec.pointer_size.raw == 4
            || dl.default_address_space_pointer_spec.pointer_size.raw == 8)
        && layouts_wf::<LocalIdx, F, FieldIdx, VariantIdx, C>(*calc, local_layouts)
)]
#[thrust_macros::ensures(variant_env_wf::<F, VariantIdx, FieldIdx, LocalIdx, C>(*calc, local_layouts, assignments))]
#[thrust::reveal(variant_env_wf)]
fn variant_env_of<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    LocalIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: &LayoutCalculator<C>,
    local_layouts: &IndexSlice<LocalIdx, F>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
) {}

/// `variant_entries_wf` at every variant `iter_enumerated` yields, from `layout()`'s `requires` on
/// the variants' entries and eligibility's properties 1, 2b and 2c over all variants, in the forms
/// these state.
#[thrust_macros::lemma]
#[thrust_macros::requires(
    forall(|v: usize, f: usize|
        0 <= v && v < (*variant_fields).len()
            && 0 <= f && f < (*variant_fields)[v].len() ==> forall(|i: USize|
            <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i) ==> i < (*local_layouts).len()))
        && forall(|v: usize, k: USize|
            0 <= v && v < (*variant_fields).len() && 0 <= k && k <= (*variant_fields)[v].len() ==> <FieldIdx as Idx>::can_new(k))
        && (*assignments).len() == (*local_layouts).len()
        // Property 1.
        && forall(|l: usize| 0 <= l && l < (*assignments).len() && (*assignments)[l] == SavedLocalEligibility::Unassigned ==> forall(|v: usize, f: usize|
            0 <= v && v < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[v].len() ==> !exists(|i: USize|
                i == l
                    && <LocalIdx as Idx>::index_is((*variant_fields)[v][f], i))))
        // Property 2b.
        && forall(|l: usize, w: usize, f: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
            0 <= l && l < (*assignments).len()
                && 0 <= w && w < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[w].len()
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][f], i))
                && (*assignments)[l] == SavedLocalEligibility::Assigned(vi) ==> forall(|vn: USize| <VariantIdx as Idx>::index_is(vi, vn) ==> vn == w))
        // Property 2c.
        && forall(|l: usize, w: usize, f: usize, g: usize, vi: <VariantIdx as thrust_models::Model>::Ty|
            0 <= l && l < (*assignments).len()
                && 0 <= w && w < (*variant_fields).len()
                && 0 <= f && f < (*variant_fields)[w].len()
                && 0 <= g && g < (*variant_fields)[w].len()
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][f], i))
                && exists(|i: USize| i == l && <LocalIdx as Idx>::index_is((*variant_fields)[w][g], i))
                && (*assignments)[l] == SavedLocalEligibility::Assigned(vi) ==> f == g)
)]
#[thrust_macros::ensures(forall(|v: USize, w: <VariantIdx as thrust_models::Model>::Ty|
    !(0 <= v && v < (*variant_fields).len() && <VariantIdx as Idx>::index_is(w, v))
    || variant_entries_wf::<F, VariantIdx, FieldIdx, LocalIdx>(local_layouts, assignments, w, &(*variant_fields)[v])))]
#[thrust::reveal(variant_entries_wf)]
fn variant_entries_of<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model,
    LocalIdx: Idx + thrust_models::Model,
>(
    local_layouts: &IndexSlice<LocalIdx, F>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>,
) {}

/// Property 3 with the bound c: an Ineligible local's field index is below c. Opaque: `layout()`
/// states it where eligibility's `ensures` gives it, with c the set's count, and carries it as one
/// atom to `variant_promoted_of`, which reveals it at the promoted fields' lengths.
#[thrust_macros::predicate]
#[thrust::opaque]
fn ineligible_below<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    c: thrust_models::model::Int,
) -> bool {
    forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
        !(0 <= l && l < (*assignments).len() && (*assignments)[l] == SavedLocalEligibility::Ineligible(x))
        || exists(|k: <FieldIdx as thrust_models::Model>::Ty|
            x == Some(k) && forall(|i: USize| !<FieldIdx as Idx>::index_is(k, i) || i < c)))
}

/// `ineligible_below` at the set's count, from eligibility's property 3 in the form it states.
#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|l: usize, x: Option<<FieldIdx as thrust_models::Model>::Ty>|
    0 <= l && l < (*assignments).len() && (*assignments)[l] == SavedLocalEligibility::Ineligible(x) ==> exists(|k: <FieldIdx as thrust_models::Model>::Ty|
        x == Some(k) && forall(|i: USize| <FieldIdx as Idx>::index_is(k, i) ==> i < DenseBitSet::<LocalIdx>::card(*ineligible_locals)))))]
#[thrust_macros::ensures(ineligible_below::<VariantIdx, FieldIdx, LocalIdx>(assignments, DenseBitSet::<LocalIdx>::card(*ineligible_locals)))]
#[thrust::reveal(ineligible_below)]
fn ineligible_below_of<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    ineligible_locals: &DenseBitSet<LocalIdx>,
) {}

/// `variant_promoted_wf` at every variant, from the facts `layout()` states of the promoted
/// fields before the closure.
#[thrust_macros::lemma]
#[thrust_macros::requires(
    ineligible_below::<VariantIdx, FieldIdx, LocalIdx>(assignments, DenseBitSet::<LocalIdx>::card(*ineligible_locals))
        && (*promoted_offsets).len() == DenseBitSet::<LocalIdx>::card(*ineligible_locals)
        && (*promoted_memory_index).len() == DenseBitSet::<LocalIdx>::card(*ineligible_locals)
        && forall(|k: USize, i: USize|
            !(0 <= k && k < (*promoted_memory_index).len() && <u32 as Idx>::index_is((*promoted_memory_index)[k], i))
                || i < (*promoted_memory_index).len())
        && forall(|vi: <VariantIdx as thrust_models::Model>::Ty|
            (*promoted_memory_index).len()
                + counts::class_cnt::<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                    *assignments, (*assignments).len(), SavedLocalEligibility::Assigned(vi))
                <= (*assignments).len())
)]
#[thrust_macros::ensures(forall(|w: <VariantIdx as thrust_models::Model>::Ty|
    variant_promoted_wf::<VariantIdx, FieldIdx, LocalIdx>(assignments, promoted_offsets, promoted_memory_index, w)))]
#[thrust::reveal(variant_promoted_wf, ineligible_below)]
fn variant_promoted_of<VariantIdx: Idx + thrust_models::Model, FieldIdx: Idx + thrust_models::Model, LocalIdx: Idx + thrust_models::Model>(
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
    ineligible_locals: &DenseBitSet<LocalIdx>,
) {}

/// The prefix a variant starts with is one `univariant` accepts in its kind: its size below the
/// object size bound (`layout_pre`), and its size plus its alignment's bytes at most `2^62`
/// (`prefix_fits`, the `repr` having no `pack`). Each is stated under the data layout `calc`
/// names, which `variant_layout` reads to drop it from the second. Opaque, as the other atoms of
/// the per-variant closure's `requires`: `prefix_wf_of` establishes it in `layout()` from the
/// prefix's `univariant` call, and `variant_layout` reveals it.
#[thrust_macros::predicate]
#[thrust::opaque]
fn prefix_wf<C: HasDataLayout>(calc: LayoutCalculator<C>, prefix_size: Size, prefix_align: AbiAlign) -> bool {
    forall(|dl: TargetDataLayout| !C::dl_of(calc, dl)
        || prefix_size.raw < obj_bound(dl))
        && forall(|dl: TargetDataLayout, q: USize, b: USize|
            !(C::dl_of(calc, dl)
                && q == prefix_align.abi.pow2
                && b == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int())
            || prefix_size.raw + b <= 4611686018427387904u64)
}

/// `prefix_wf` from the bounds it names.
#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|dl: TargetDataLayout| !C::dl_of(*calc, dl)
        || prefix_size.raw < obj_bound(dl))
        && forall(|dl: TargetDataLayout, q: USize, b: USize|
            !(C::dl_of(*calc, dl)
                && q == prefix_align.abi.pow2
                && b == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int())
            || prefix_size.raw + b <= 4611686018427387904u64))]
#[thrust_macros::ensures(prefix_wf::<C>(*calc, prefix_size, prefix_align))]
#[thrust::reveal(prefix_wf)]
fn prefix_wf_of<C: HasDataLayout>(calc: &LayoutCalculator<C>, prefix_size: Size, prefix_align: AbiAlign) {}

// Fallback: `prefix_wf_of` with its `requires` assumed, for its call in `layout()`, where the
// solver does not answer that `requires` even right after an `assume!` of it. A checked wrapper,
// as `map_new_assumed` of thrust/iter.rs; call `prefix_wf_of` again once the solver
// answers it there.
#[thrust_macros::context]
#[thrust_macros::lemma]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(prefix_wf::<C>(*calc, prefix_size, prefix_align))]
fn prefix_wf_of_assumed<C: HasDataLayout>(calc: &LayoutCalculator<C>, prefix_size: Size, prefix_align: AbiAlign) {
    thrust_macros::assume!(
        |calc: &LayoutCalculator<C>, prefix_size: Size, prefix_align: AbiAlign|
            forall(|dl: TargetDataLayout| !C::dl_of(*calc, dl)
                || prefix_size.raw < obj_bound(dl))
                && forall(|dl: TargetDataLayout, q: USize, b: USize|
                    !(C::dl_of(*calc, dl)
                        && q == prefix_align.abi.pow2
                        && b == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int())
                    || prefix_size.raw + b <= 4611686018427387904u64)
    );
    prefix_wf_of(calc, prefix_size, prefix_align);
}

/// A layout `univariant` returns for fields that fit in any order has its size plus its
/// alignment's bytes at most `2^62`: its size and `2^q`, which bound the bytes `1 << (q & 63)`
/// (`bytes_within`), are each below the fields' weighs sum (univariant's `ensures`), which
/// `fits_in_any_order` puts below the object size bound, at most `2^61`.
#[thrust_macros::lemma]
#[thrust_macros::requires(LayoutCalculator::<C>::fits_in_any_order::<FieldIdx, VariantIdx, F>(*calc, fields, repr, kind))]
#[thrust_macros::requires(forall(|dl: TargetDataLayout, s: USize, q: USize|
    C::dl_of(*calc, dl)
        && LayoutCalculator::<C>::weighs::<FieldIdx, VariantIdx, F>(fields, repr, kind, dl, s)
        && q == align.abi.pow2 ==> (size.raw < s && pow2(q) <= s)))]
#[thrust_macros::ensures(forall(|dl: TargetDataLayout, q: USize, b: USize|
    !(C::dl_of(*calc, dl)
        && q == align.abi.pow2
        && b == (BitVec::<64, false>::from_int(1) << (BitVec::from_int(q) & BitVec::from_int(63))).to_int())
    || size.raw + b <= 4611686018427387904u64))]
#[thrust::reveal(super::LayoutCalculator::fits_in_any_order)]
fn prefix_fits_bound<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + Copy + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    C: HasDataLayout,
>(
    calc: &LayoutCalculator<C>,
    fields: &IndexVec<FieldIdx, F>,
    repr: &ReprOptions,
    kind: StructKind,
    size: Size,
    align: AbiAlign,
) {
    super::bytes_within(align.abi.pow2 as u64);
}

/// The variant's fields fit in any order after the prefix: `univariant`'s `fits_in_any_order` for
/// every field list that holds, in order, the layouts of a selection of the variant's entries
/// Assigned to it (`counts::selection_of`), with a `repr` without alignment (that of
/// `ReprOptions::default()`) and the prefix's size and alignment. Opaque, as the other atoms of the
/// per-variant closure's `requires`: `layout()` assumes it, where rustc's code makes it true, and
/// `variant_layout` reveals it at its fields.
#[thrust_macros::predicate]
#[thrust::opaque]
fn variant_fits_wf<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    LocalIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: LayoutCalculator<C>,
    local_layouts: &IndexSlice<LocalIdx, F>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    index: VariantIdx,
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
    prefix_size: Size,
    prefix_align: AbiAlign,
) -> bool {
    forall(|fs: thrust_models::model::Seq<<F as thrust_models::Model>::Ty>, rp: ReprOptions|
        !(rp.align == None
            && counts::selection_of::<FieldIdx, LocalIdx, LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>, F>(
                &fs, *variant_fields, *assignments, SavedLocalEligibility::Assigned(index), local_layouts))
        || LayoutCalculator::<C>::fits_in_any_order::<FieldIdx, VariantIdx, F>(
            calc, &fs, &rp, StructKind::Prefixed(prefix_size, prefix_align.abi)))
}

// Rewrite (rewrites.md R17): the body of `layout()`'s per-variant closure, as a function whose
// `requires` is the closure's, the four atoms above, which it reveals. The closure keeps the
// updates of `size` and `align` and the `VariantLayout`, so its `requires` and `Map::new`'s
// precondition over the variants read four atoms instead of the facts they stand for.
#[thrust_macros::requires(
    variant_env_wf::<F, VariantIdx, FieldIdx, LocalIdx, C>(*calc, local_layouts, assignments)
        && variant_entries_wf::<F, VariantIdx, FieldIdx, LocalIdx>(local_layouts, assignments, index, variant_fields)
        && variant_promoted_wf::<VariantIdx, FieldIdx, LocalIdx>(assignments, promoted_offsets, promoted_memory_index, index)
        && variant_fits_wf::<F, VariantIdx, FieldIdx, LocalIdx, C>(*calc, local_layouts, assignments, index, variant_fields, prefix_size, prefix_align)
        && prefix_wf::<C>(*calc, prefix_size, prefix_align)
)]
#[thrust_macros::ensures(forall(|l: LayoutData<FieldIdx, VariantIdx>|
    result != Ok(l) || matches!(l.fields, FieldsShape::Arbitrary { .. })))]
#[thrust_macros::context]
#[thrust::reveal(variant_env_wf, variant_entries_wf, variant_promoted_wf, variant_fits_wf, prefix_wf)]
fn variant_layout<
    'a,
    F: core::ops::Deref<Target = &'a LayoutData<FieldIdx, VariantIdx>> + core::fmt::Debug + Copy + thrust_models::Model<Ty: PartialEq>,
    VariantIdx: Idx + thrust_models::Model,
    FieldIdx: Idx + thrust_models::Model<Ty: PartialEq>,
    LocalIdx: Idx + thrust_models::Model,
    C: HasDataLayout,
>(
    calc: &LayoutCalculator<C>,
    local_layouts: &IndexSlice<LocalIdx, F>,
    assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
    promoted_offsets: &IndexVec<FieldIdx, Size>,
    promoted_memory_index: &IndexVec<FieldIdx, u32>,
    prefix_size: Size,
    prefix_align: AbiAlign,
    index: VariantIdx,
    variant_fields: &IndexVec<FieldIdx, LocalIdx>,
) -> Result<LayoutData<FieldIdx, VariantIdx>, crate::rustc_abi::layout::LayoutCalculatorError<F>> {
    // What `combine_offsets` requires of the variant's entries and the promoted fields, in its
    // forms, from the `requires`, at the start, and as the atom `combine_wf`, which reaches the
    // call unchanged.
    thrust_macros::proof_assert!(|variant_fields: &IndexVec<FieldIdx, LocalIdx>|
        forall(|k: USize| 0 <= k && k <= (*variant_fields).len() ==> <FieldIdx as Idx>::can_new(k)));
    thrust_macros::proof_assert!(|variant_fields: &IndexVec<FieldIdx, LocalIdx>, assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>|
        forall(|f: usize, i: USize|
            0 <= f && f < (*variant_fields).len() && <LocalIdx as Idx>::index_is((*variant_fields)[f], i)
                ==> (i < (*assignments).len() && (*assignments)[i] != SavedLocalEligibility::Unassigned)));
    thrust_macros::proof_assert!(|assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, promoted_offsets: &IndexVec<FieldIdx, Size>, promoted_memory_index: &IndexVec<FieldIdx, u32>|
        ineligible_promoted::<VariantIdx, FieldIdx, LocalIdx>(assignments, promoted_offsets, promoted_memory_index)
            && forall(|k: USize, i: USize|
                0 <= k && k < (*promoted_memory_index).len() && <u32 as Idx>::index_is((*promoted_memory_index)[k], i)
                    ==> i < (*promoted_memory_index).len()));
    thrust_macros::proof!(combine_wf_of(variant_fields, assignments, promoted_offsets, promoted_memory_index));
    // Rewrite (rewrites.md R14): the variant's fields, the layouts of the entries whose local
    // is Assigned to the variant, are collected by `variant_field_layouts`. Its `requires`
    // holds by the `requires`; its `ensures` gives the count sites 1 and 3 need (with the
    // `requires` on c) and that each field is a layout of `local_layouts`, which `univariant`'s
    // `layout_pre` reads.
    let fields = variant_field_layouts(variant_fields, assignments, index, local_layouts);
    // Rewrite (rewrites.md R13): the number m of the fields is bound to a name, for the cuts
    // below and `combine_offsets`.
    let m = fields.len();
    // c + m <= n: `variant_field_layouts`' count with the `requires` on c.
    thrust_macros::proof_assert!(|promoted_memory_index: &IndexVec<FieldIdx, u32>, m: usize, local_layouts: &IndexSlice<LocalIdx, F>|
        (*promoted_memory_index).len() + m <= (*local_layouts).len());

    // Rewrite (rewrites.md R13): the arguments are bound to names, for the `assume!`.
    let repr = ReprOptions::default();
    let kind = StructKind::Prefixed(prefix_size, prefix_align.abi);
    // `univariant`'s `fits_in_any_order` for the variant: `variant_fits_wf` at the fields, which
    // `variant_field_layouts` gives as the layouts of a selection of the entries Assigned to the
    // variant, and `repr`, which has no alignment.
    thrust_macros::proof_assert!(
        |calc: &LayoutCalculator<C>, fields: IndexVec<FieldIdx, F>, repr: ReprOptions, kind: StructKind|
            LayoutCalculator::<C>::fits_in_any_order::<FieldIdx, VariantIdx, F>(*calc, &fields, &repr, kind)
    );
    thrust_macros::proof!(layouts_wf_of_entries(calc, local_layouts, &fields));
    thrust_macros::proof!(layout_pre_of_wf(calc, &fields, kind));
    // `variant_fits_wf` holds for a `repr` without alignment: `repr` has none.
    thrust_macros::proof_assert!(|repr: ReprOptions| repr.align == None);
    // Rewrite (rewrites.md R17): the data layout is read, so that `prefix_wf`'s bound of the
    // prefix's size and alignment, stated under it, gives `univariant`'s `prefix_fits`, which names
    // no data layout; `repr` has no `pack`.
    let dl = calc.cx.data_layout();
    thrust_macros::proof_assert!(|repr: ReprOptions, kind: StructKind, dl: &TargetDataLayout|
        repr.pack == None && LayoutCalculator::<C>::prefix_fits(&repr, kind));
    let mut variant = calc.univariant(&fields, &repr, kind)?;

    // `combine_offsets` requires `u32` to reach the variant's m fields.
    thrust_macros::proof_assert!(|m: usize|
        forall(|k: USize| 0 <= k && k <= m ==> <u32 as Idx>::can_new(k)));
    // `FieldIdx` and `u32` reach c + m, by c + m <= n; the fields are `Arbitrary` with m offsets
    // (univariant's `ensures`).
    thrust_macros::proof_assert!(|promoted_memory_index: &IndexVec<FieldIdx, u32>, m: usize|
        forall(|k: USize| 0 <= k && k <= (*promoted_memory_index).len() + m ==> <FieldIdx as Idx>::can_new(k))
            && (*promoted_memory_index).len() + m <= 4294967295usize);
    thrust_macros::proof_assert!(|variant: LayoutData<FieldIdx, VariantIdx>, m: usize|
        FieldsShape::<FieldIdx>::arbitrary_of(variant.fields, m));
    thrust_macros::proof_assert!(|variant_fields: &IndexVec<FieldIdx, LocalIdx>, assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, index: VariantIdx, m: usize|
        assigned_count::<FieldIdx, LocalIdx, VariantIdx>(variant_fields, assignments, index, m));
    // Property 2b (the `requires`) in the form `combine_offsets` requires: an entry's local
    // Assigned to some variant is Assigned to this one (`index_is_injective`).
    thrust_macros::proof_assert!(|variant_fields: &IndexVec<FieldIdx, LocalIdx>, assignments: &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, index: VariantIdx|
        forall(|f: usize, v: <VariantIdx as thrust_models::Model>::Ty|
            0 <= f && f < (*variant_fields).len()
                && (*assignments)[<LocalIdx as Idx>::index_logic((*variant_fields)[f])] == SavedLocalEligibility::Assigned(v)
                ==> v == index));

    // Rewrite (rewrites.md R12): the destructuring of the variant's fields and the
    // combination of its offsets and memory order with the promoted ones are
    // `combine_offsets`, which takes the number m of the variant's fields. Its `requires`
    // holds by univariant's `arbitrary_of`, by `variant_field_layouts`' count with the
    // `requires` on c (c + m <= n, so `FieldIdx` and `u32` reach c + m), by the `requires`
    // (properties 1 and 3 and the bounds of the variant's entries) and by
    // `variant_field_layouts`' count of m.
    let (combined_offsets, combined_in_memory_order) = combine_offsets(
        variant_fields,
        assignments,
        index,
        promoted_offsets,
        promoted_memory_index,
        variant.fields,
        m,
    );

    variant.fields = FieldsShape::Arbitrary {
        offsets: combined_offsets,
        in_memory_order: combined_in_memory_order,
    };
    Ok(variant)
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
//   requires; `layout_wf` of every layout `univariant` may receive: `niche_wf` of its
//   largest niche, and the niche within that layout; `Scalar::wf_in` of the layout if its
//   `backend_repr` is a scalar (`scalar_pair`); and its size below
//   the object size bound, which every layout `rustc_abi` computes is checked against
//   (`univariant_biased`, `layout_of_enum`, `checked_add`, `checked_mul`). These layouts are each of `local_layouts` and `prefix_layouts`
//   (`layouts_wf`), and `tag_to_layout`'s result for any such integer scalar (through its
//   postcondition), each named by `post!` of `Deref::deref`. `F`'s `deref` is a function (`deref_functional`), which `univariant`
//   requires; rustc's `Layout` dereferences to the interned pointer it holds.
// - Not guaranteed by the caller:
//   - `FieldIdx` can be built up to P + 1 + n (the prefix, the tag and at most n promoted
//     locals), and P + 1 + n <= u32::MAX, for the `u32` memory order. The panic condition is
//     P + 1 + c with c the number of ineligible locals (`DenseBitSet::card` of
//     `ineligible_locals`): c is computed inside, from eligibility's result, so a condition on
//     the inputs can only bound it by n. rustc's index types are bounded by 0xFFFF_FF00, so a
//     coroutine with P + 1 + n above that is excluded, also when P + 1 + c is not.
//   - The size bound: with T the weight (`weight`: each layout's size and twice its alignment)
//     of `prefix_layouts`, the layout `tag_to_layout` gives for the tag `layout()` builds (an
//     integer of valid range 0 to V - 1) and all of `local_layouts`, plus the aggregate and
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
        && layouts_wf::<LocalIdx, F, FieldIdx, VariantIdx, C>(*calc, local_layouts)
        && layouts_wf::<FieldIdx, F, FieldIdx, VariantIdx, C>(*calc, &prefix_layouts)
        && forall(|ti: Integer, tg: WrappingRange, s: Scalar, r: <F as thrust_models::Model>::Ty|
            s == Scalar::Initialized { value: Primitive::Int(ti, false), valid_range: tg }
                && thrust_macros::post!(tag_to_layout(s), r) ==> layout_wf::<F, FieldIdx, VariantIdx, C>(*calc, r))
        && forall(|ti: Integer, tg: WrappingRange| thrust_macros::pre!(tag_to_layout(Scalar::Initialized { value: Primitive::Int(ti, false), valid_range: tg })))
        && forall(|dl: TargetDataLayout, ti: Integer, tg: WrappingRange, s: Scalar, r: <F as thrust_models::Model>::Ty, l: LayoutData<FieldIdx, VariantIdx>, d: &&LayoutData<FieldIdx, VariantIdx>|
            C::dl_of(*calc, dl) && tg.start == 0 && tg.end + 1 == (*variant_fields).len()
                && s == Scalar::Initialized { value: Primitive::Int(ti, false), valid_range: tg } && thrust_macros::post!(tag_to_layout(s), r) && thrust_macros::post!(<F as core::ops::Deref>::deref(&r), d) && **d == l ==> exists(|wp: USize, wl: USize, q: USize, qa: USize, qi: USize, b: USize|
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
// No predicate is revealed: `layout()` establishes `layout_pre` with `layout_pre_of_wf` at both
// `univariant` calls and only assumes `fits_in_any_order` (the `assume!` at the prefix and that of
// `variant_fits_wf` for the variants), and passes
// `arbitrary_of` from `univariant`'s `ensures` to `split_prefix_fields` and `combine_offsets`,
// which reveal it, so it reads each as the atom these state.
pub fn layout<
    'a,
    // `Ty: PartialEq`, as `fits_in_any_order` bounds it, for the two `assume!`s that state it.
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
    // The first two atoms of the per-variant closure's `requires` (R17), where `layout()` has
    // their facts: its `requires` and eligibility's `ensures`.
    thrust_macros::proof!(variant_env_of(calc, local_layouts, &assignments));
    thrust_macros::proof!(variant_entries_of(local_layouts, &assignments, variant_fields));
    thrust_macros::proof!(ineligible_below_of(&assignments, &ineligible_locals));

    let tag_index = prefix_layouts.next_index();
    thrust_macros::proof!(index_is_only(&tag_index, prefix_layouts.len()));

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

    // Rewrite (rewrites.md R13): the tag's layout is bound to a name, for `promote_locals`.
    let tag_layout = tag_to_layout(tag);
    // `layout()`'s `requires` of the tag's layout.
    thrust_macros::proof_assert!(|calc: &LayoutCalculator<C>, tag_layout: F|
        layout_wf::<F, FieldIdx, VariantIdx, C>(*calc, tag_layout));
    // Rewrite (rewrites.md R15): the `push` of the tag's layout and the `extend` by the promoted
    // locals' layouts are `promote_locals`. Its `requires` holds by `layout()`'s `requires`
    // (`FieldIdx` reaches P + 1 + n; `layouts_wf` of the entry fields and of `local_layouts`),
    // eligibility's `ensures` (the set is over the n locals) and the step above.
    promote_locals(calc, &mut prefix_layouts, tag_layout, &ineligible_locals, local_layouts);
    // Rewrite (rewrites.md R13): the `repr` argument is bound to a name, for the `assume!`.
    let repr = ReprOptions::default();
    // Assumed (not proved): `univariant`'s `fits_in_any_order` for the prefix. rustc's code makes
    // it true under `layout()`'s size bound: the prefix's fields are the entry `prefix_layouts`,
    // the tag's layout and the promoted locals, which are distinct locals (the set's members,
    // each yielded once, increasing), so their weight is at most that of `prefix_layouts`, the tag
    // and all of `local_layouts`, T in the size bound, and 3T + 2^qa + 2^qi < b gives the prefix's
    // weighs sum below b. Not proved: `weight` is an existential over a `Seq<Int>` of the fields'
    // weights (a field's weight is read through `deref`'s postcondition, a relation), and the
    // solver does not answer such a goal even with its witness named (fork issue #278), nor can a
    // proof name the witness of the `weight`s `layout()` requires.
    thrust_macros::assume!(
        |calc: &LayoutCalculator<C>, prefix_layouts: IndexVec<FieldIdx, F>, repr: ReprOptions|
            LayoutCalculator::<C>::fits_in_any_order::<FieldIdx, VariantIdx, F>(*calc, &prefix_layouts, &repr, StructKind::AlwaysSized)
    );
    // Reachability twin of the `assume!` (fail root layout_reach_prefix.rs): the path after it is
    // reachable, so the `assume!` makes no proof here vacuous.
    #[cfg(thrust_layout_reach_prefix)]
    thrust_macros::proof_assert!(|| false);
    thrust_macros::proof!(layout_pre_of_wf(calc, &prefix_layouts, StructKind::AlwaysSized));
    let prefix = calc.univariant(
        &prefix_layouts,
        &repr,
        StructKind::AlwaysSized,
    )?;

    let (prefix_size, prefix_align) = (prefix.size, prefix.align);
    // The prefix's size is bounded as `layout_pre` reads the variants' kind (univariant's
    // `ensures`), and its size plus its alignment's bytes as `prefix_fits` does (univariant's
    // `ensures` under the `fits_in_any_order` assumed above): the fifth atom of the per-variant
    // closure's `requires`.
    thrust_macros::proof!(prefix_fits_bound(calc, &prefix_layouts, &repr, StructKind::AlwaysSized, prefix_size, prefix_align));
    // Fallback: through `prefix_wf_of_assumed`, which assumes `prefix_wf_of`'s precondition.
    thrust_macros::proof!(prefix_wf_of_assumed(calc, prefix_size, prefix_align));
    // Assumed (not proved): each variant's fields fit in any order after the prefix
    // (`variant_fits_wf`, `univariant`'s `fits_in_any_order` for the variant's `univariant` call).
    // rustc's code makes it true under `layout()`'s size bound (its header comment): a variant's
    // weighs sum is the weight of its fields plus the prefix's size and twice its alignment, each
    // below the prefix's weighs sum S_p (univariant's `ensures`), so it is below
    // (Assigned) + 3 S_p + 2^qa + 2^qi, with (Assigned) the weight of the variant's fields. Those
    // are the layouts of the locals Assigned to the variant, each once (properties 2b and 2c).
    // S_p is at most the weight of the entry `prefix_layouts`, the tag and the promoted locals,
    // and the promoted locals are Ineligible (property 4), so disjoint from the Assigned ones:
    // (Assigned) + 3 (promoted) <= 3 (weight of `local_layouts`), and the sum is below
    // 3T + 2^qa + 2^qi < b. Not proved: as at the prefix, the witness of `weight` for a selection
    // of `local_layouts` (fork issue #278).
    thrust_macros::assume!(
        |calc: &LayoutCalculator<C>, local_layouts: &IndexSlice<LocalIdx, F>, assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
            variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, prefix_size: Size, prefix_align: AbiAlign|
            forall(|v: USize, w: <VariantIdx as thrust_models::Model>::Ty|
                !(0 <= v && v < (*variant_fields).len() && <VariantIdx as Idx>::index_is(w, v))
                || variant_fits_wf::<F, VariantIdx, FieldIdx, LocalIdx, C>(
                    *calc, local_layouts, &assignments, w, &(*variant_fields)[v], prefix_size, prefix_align))
    );
    // Reachability twin of the `assume!` (fail root layout_reach_variant.rs): the path after it is
    // reachable, so the `assume!` makes no proof here vacuous.
    #[cfg(thrust_layout_reach_variant)]
    thrust_macros::proof_assert!(|| false);

    // Rewrite (rewrites.md R16): the `match` that splits the prefix's offsets and memory order at
    // the promoted fields is `split_prefix_fields`. Its `requires` holds by univariant's
    // `arbitrary_of` with n = P + 1 + c entries (`promote_locals`), `next_index` and `layout()`'s
    // `requires` (`FieldIdx` and `u32` reach n, as c is at most the n locals).
    thrust_macros::proof_assert!(|prefix: LayoutData<FieldIdx, VariantIdx>, prefix_layouts: IndexVec<FieldIdx, F>|
        FieldsShape::<FieldIdx>::arbitrary_of(prefix.fields, prefix_layouts.len()));
    thrust_macros::proof_assert!(|tag_index: FieldIdx, prefix_layouts: IndexVec<FieldIdx, F>|
        forall(|t: USize| <FieldIdx as Idx>::index_is(tag_index, t) ==> t + 1 <= prefix_layouts.len()));
    thrust_macros::proof_assert!(|prefix_layouts: IndexVec<FieldIdx, F>|
        prefix_layouts.len() <= 4294967295usize);
    let (outer_fields, promoted_offsets, promoted_memory_index) =
        split_prefix_fields(prefix.fields, tag_index, prefix_layouts.len());

    let mut size = prefix.size;
    let mut align = prefix.align;
    // The per-variant closure's `requires`, four atoms (R17; the fourth, `variant_fits_wf`, is
    // assumed above); the third here: the promoted fields'
    // lengths are the set's count c (`split_prefix_fields` at the tag index P, with P + 1 + c
    // fields), so property 3 below c (`ineligible_below`) gives `ineligible_promoted`; c and the
    // locals Assigned to any variant are at most n (`ones_assigned_disjoint` and `card_ones`).
    thrust_macros::proof_assert!(|promoted_offsets: IndexVec<FieldIdx, Size>, promoted_memory_index: IndexVec<FieldIdx, u32>, ineligible_locals: DenseBitSet<LocalIdx>|
        promoted_offsets.len() == DenseBitSet::<LocalIdx>::card(ineligible_locals)
            && promoted_memory_index.len() == DenseBitSet::<LocalIdx>::card(ineligible_locals));
    thrust_macros::proof_assert!(|assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, promoted_memory_index: IndexVec<FieldIdx, u32>|
        forall(|vi: <VariantIdx as thrust_models::Model>::Ty|
            promoted_memory_index.len()
                + counts::class_cnt::<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>(
                    assignments, assignments.len(), SavedLocalEligibility::Assigned(vi))
                <= assignments.len()));
    thrust_macros::proof_assert!(|promoted_memory_index: IndexVec<FieldIdx, u32>|
        forall(|k: USize, i: USize|
            !(0 <= k && k < promoted_memory_index.len() && <u32 as Idx>::index_is(promoted_memory_index[k], i))
                || i < promoted_memory_index.len()));
    thrust_macros::proof!(variant_promoted_of(&assignments, &promoted_offsets, &promoted_memory_index, &ineligible_locals));
    // Rewrite (rewrites.md R13): the variants' iterator is bound to a name, so that the atoms of
    // the closure's `requires` are premises of `Map::new`'s precondition, stated right before it.
    let variant_iter = variant_fields.iter_enumerated();
    // The variant an item of the iterator is, at every position, for `Map::new`'s
    // `preservation_inv`: the closure's `requires` at the last of the items produced.
    thrust_macros::proof!(IterEnumerated::yields_last(&variant_iter));
    thrust_macros::proof_assert!(|variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>|
        forall(|k: USize| 0 <= k && k <= (*variant_fields).len() ==> <VariantIdx as Idx>::can_new(k)));
    thrust_macros::proof_assert!(|calc: &LayoutCalculator<C>, local_layouts: &IndexSlice<LocalIdx, F>, assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>|
        variant_env_wf::<F, VariantIdx, FieldIdx, LocalIdx, C>(*calc, local_layouts, &assignments));
    thrust_macros::proof_assert!(|local_layouts: &IndexSlice<LocalIdx, F>, assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>|
        forall(|v: USize, w: <VariantIdx as thrust_models::Model>::Ty|
            !(0 <= v && v < (*variant_fields).len() && <VariantIdx as Idx>::index_is(w, v))
            || variant_entries_wf::<F, VariantIdx, FieldIdx, LocalIdx>(local_layouts, &assignments, w, &(*variant_fields)[v])));
    thrust_macros::proof_assert!(|assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>, promoted_offsets: IndexVec<FieldIdx, Size>, promoted_memory_index: IndexVec<FieldIdx, u32>|
        forall(|w: <VariantIdx as thrust_models::Model>::Ty|
            variant_promoted_wf::<VariantIdx, FieldIdx, LocalIdx>(&assignments, &promoted_offsets, &promoted_memory_index, w)));
    thrust_macros::proof_assert!(|calc: &LayoutCalculator<C>, local_layouts: &IndexSlice<LocalIdx, F>, assignments: IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
            variant_fields: &IndexSlice<VariantIdx, IndexVec<FieldIdx, LocalIdx>>, prefix_size: Size, prefix_align: AbiAlign|
        forall(|v: USize, w: <VariantIdx as thrust_models::Model>::Ty|
            !(0 <= v && v < (*variant_fields).len() && <VariantIdx as Idx>::index_is(w, v))
            || variant_fits_wf::<F, VariantIdx, FieldIdx, LocalIdx, C>(
                *calc, local_layouts, &assignments, w, &(*variant_fields)[v], prefix_size, prefix_align)));
    thrust_macros::proof_assert!(|calc: &LayoutCalculator<C>, prefix_size: Size, prefix_align: AbiAlign|
        prefix_wf::<C>(*calc, prefix_size, prefix_align));
    // Rewrite (rewrites.md R8): `Map::new(it, f)` for `it.map(f)` and `collect_index_vec_result`
    // for the `collect` at the end of this expression.
    // The per-variant closure's contract: its `requires` is `variant_layout`'s (R17), the atoms
    // above at the variant it is given. Its `ensures` is `true`: `layout()` states nothing of the
    // variants it returns. The closure is `FnMut` (it updates `size` and `align`), so a clause
    // reads each capture through the receiver, as `&mut` of the type it is captured by. No
    // `hist_inv` bounds `size` and `align`: nothing after the `collect` needs a bound, as
    // `Size::align_to` requires nothing (its body checked by the `values.rs` root) and `max`
    // neither.
    // Fallback: through `map_new_assumed`, which assumes `Map::new`'s precondition (the map's
    // `inv`), as the solver does not answer it; call `Map::new` again once it does. `collect`'s
    // precondition, the same `inv`, is `map_new_assumed`'s `ensures`.
    let variants = collect_index_vec_result::<VariantIdx, _, _, _>(map_new_assumed(
        variant_iter,
        thrust_macros::closure!(
        captures(
            calc: &mut &LayoutCalculator<C>,
            local_layouts: &mut &IndexSlice<LocalIdx, F>,
            assignments: &mut &IndexVec<LocalIdx, SavedLocalEligibility<VariantIdx, FieldIdx>>,
            promoted_offsets: &mut &IndexVec<FieldIdx, Size>,
            promoted_memory_index: &mut &IndexVec<FieldIdx, u32>,
            prefix_size: &mut &Size,
            prefix_align: &mut &AbiAlign,
        ),
        requires(
            variant_env_wf::<F, VariantIdx, FieldIdx, LocalIdx, C>(**calc, *local_layouts, *assignments)
                && variant_entries_wf::<F, VariantIdx, FieldIdx, LocalIdx>(*local_layouts, *assignments, index, variant_fields)
                && variant_promoted_wf::<VariantIdx, FieldIdx, LocalIdx>(
                    *assignments, *promoted_offsets, *promoted_memory_index, index)
                && variant_fits_wf::<F, VariantIdx, FieldIdx, LocalIdx, C>(
                    **calc, *local_layouts, *assignments, index, variant_fields, **prefix_size, **prefix_align)
                && prefix_wf::<C>(**calc, **prefix_size, **prefix_align)
        ),
        ensures(true),
        |(index, variant_fields): (VariantIdx, &IndexVec<FieldIdx, LocalIdx>)|
            -> Result<VariantLayout<FieldIdx>, crate::rustc_abi::layout::LayoutCalculatorError<F>> {
            // Rewrite (rewrites.md R17): the variant's layout is `variant_layout`.
            let variant = variant_layout(
                calc,
                local_layouts,
                &assignments,
                &promoted_offsets,
                &promoted_memory_index,
                prefix_size,
                prefix_align,
                index,
                variant_fields,
            )?;

            size = size.max(variant.size);
            align = align.max(variant.align);
            // `VariantLayout::from_layout` requires `Arbitrary` fields: `variant_layout`'s
            // `ensures`.
            Ok(VariantLayout::from_layout(variant))
        },
        ),
    ))?;
    // Reachability twin of the fallback's assumptions in this function (fail root
    // layout_reach_fallback.rs).
    #[cfg(thrust_layout_reach_fallback)]
    thrust_macros::proof_assert!(|| false);

    size = size.align_to(align.abi);

    // Rewrite (rewrites.md R8): `iter_all(it, f)` for `it.all(f)`.
    // The closure's contract is written, so `iter_all`'s `pre_all` reads `true` rather than an
    // inferred precondition.
    let uninhabited = prefix.uninhabited
        || iter_all(
            variants.iter(),
            thrust_macros::closure!(requires(true), ensures(true), |v: &VariantLayout<FieldIdx>| -> bool { v.is_uninhabited() }),
        );
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
