//! The weight of a selection of indices: when a sequence of indices has no index twice, the
//! entries of a non-negative weight sequence at those indices sum to at most the whole sum
//! (`weight_at_le_distinct`). The sums are recursive logic functions over the model of an
//! `IndexVec<u32, I>`, read through `Idx::index_logic` as in `lemmas`, and the lemmas prove the
//! bound by induction: the weighted form of the counting lemmas L3 and L5 of `lemmas`, with the
//! weights `ts` a parameter of each lemma. A bit iterator's `produces` states that the indices of
//! one `visited` sequence are pairwise distinct, which `lemmas::distinct_of_injective` turns into
//! the `distinct` this bound needs.

use crate::thrust_models;
use thrust_models::model::{Int, Seq};
use thrust_models::{forall, Ghost};

use crate::case_study::lemmas::{distinct, l4_all, occ};
use crate::case_study::USize;
use crate::rustc_index::{Idx, IndexVec};

/// The sum of the first `k` entries of `ts`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn weight_first(ts: Seq<Int>, k: USize) -> Int {
    if k <= 0 { 0 } else { weight_first(ts, k - 1) + ts[k - 1] }
}

/// The sum of the entries of `ts` at the indices the first `k` entries of `s` hold.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn weight_at<I: Idx + thrust_models::Model>(ts: Seq<Int>, s: IndexVec<u32, I>, k: USize) -> Int {
    if k <= 0 { 0 } else { weight_at::<I>(ts, s, k - 1) + ts[I::index_logic(s[k - 1])] }
}

/// As `weight_at`, over the entries whose index is below `b`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn weight_below<I: Idx + thrust_models::Model>(ts: Seq<Int>, s: IndexVec<u32, I>, k: USize, b: USize) -> Int {
    if k <= 0 {
        0
    } else if I::index_logic(s[k - 1]) < b {
        weight_below::<I>(ts, s, k - 1, b) + ts[I::index_logic(s[k - 1])]
    } else {
        weight_below::<I>(ts, s, k - 1, b)
    }
}

/// As `weight_at`, over the entries whose index is `x`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn weight_of<I: Idx + thrust_models::Model>(ts: Seq<Int>, s: IndexVec<u32, I>, k: USize, x: USize) -> Int {
    if k <= 0 {
        0
    } else if I::index_logic(s[k - 1]) == x {
        weight_of::<I>(ts, s, k - 1, x) + ts[x]
    } else {
        weight_of::<I>(ts, s, k - 1, x)
    }
}

/// The weighted L3: a bound one higher adds the weight of the entries at the bound.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(weight_below::<I>(ts, s, k, b + 1) == weight_below::<I>(ts, s, k, b) + weight_of::<I>(ts, s, k, b))]
pub fn weight_l3<I: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, s: Ghost<IndexVec<u32, I>>, k: usize, b: usize) {
    if k > 0 {
        weight_l3(ts, s, k - 1, b);
    }
}

/// An index with no entry has no weight, and one with at most one entry has at most its own, which
/// is not negative.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(0 <= ts[x])]
#[thrust_macros::ensures(
    (occ::<I>(x, s, k) != 0 || weight_of::<I>(ts, s, k, x) == 0)
        && (occ::<I>(x, s, k) > 1 || weight_of::<I>(ts, s, k, x) <= (ts)[x])
)]
pub fn weight_of_le<I: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, s: Ghost<IndexVec<u32, I>>, k: usize, x: usize) {
    if k > 0 {
        weight_of_le(ts, s, k - 1, x);
    }
}

/// No entry is below 0.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(b == 0)]
#[thrust_macros::ensures(weight_below::<I>(ts, s, k, b) == 0)]
pub fn weight_l0<I: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, s: Ghost<IndexVec<u32, I>>, k: usize, b: usize) {
    if k > 0 {
        weight_l0(ts, s, k - 1, b);
    }
}

/// The weighted L5: when every index below `b` occurs at most once, the entries below `b` weigh at
/// most the first `b` entries of `ts`, none of which is negative.
#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::requires(forall(|x: USize| x < b ==> occ::<I>(x, s, k) <= 1))]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < b) || 0 <= (ts)[x]))]
#[thrust_macros::ensures(weight_below::<I>(ts, s, k, b) <= weight_first(ts, b))]
pub fn weight_l5<I: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, s: Ghost<IndexVec<u32, I>>, k: usize, b: usize) {
    if b > 0 {
        weight_l5(ts, s, k, b - 1);
        weight_l3(ts, s, k, b - 1);
        weight_of_le(ts, s, k, b - 1);
    } else {
        weight_l0(ts, s, k, b);
    }
}

/// Entries all below `n` are all counted below `n`.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|j: Int| !(0 <= j && j < k) || I::index_logic(s[j]) < n))]
#[thrust_macros::ensures(weight_below::<I>(ts, s, k, n) == weight_at::<I>(ts, s, k))]
pub fn weight_all_below<I: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, s: Ghost<IndexVec<u32, I>>, k: usize, n: usize) {
    if k > 0 {
        weight_all_below(ts, s, k - 1, n);
    }
}

/// The weights at the indices of `k` distinct entries below `n` sum to at most the first `n`
/// entries of `ts`, none of which is negative: a selection that yields no index twice weighs no
/// more than everything.
#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|x: USize| occ::<I>(x, s, k) <= 1))]
#[thrust_macros::requires(forall(|j: Int| !(0 <= j && j < k) || I::index_logic(s[j]) < n))]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < n) || 0 <= (ts)[x]))]
#[thrust_macros::ensures(weight_at::<I>(ts, s, k) <= weight_first(ts, n))]
pub fn weight_at_le<I: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, s: Ghost<IndexVec<u32, I>>, k: usize, n: usize) {
    weight_l5(ts, s, k, n);
    weight_all_below(ts, s, k, n);
}

/// `weight_at_le` for `k` distinct entries.
#[thrust_macros::lemma]
#[thrust_macros::requires(distinct::<I>(s, k))]
#[thrust_macros::requires(forall(|j: Int| !(0 <= j && j < k) || I::index_logic(s[j]) < n))]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < n) || 0 <= (ts)[x]))]
#[thrust_macros::ensures(weight_at::<I>(ts, s, k) <= weight_first(ts, n))]
pub fn weight_at_le_distinct<I: Idx + thrust_models::Model>(s: Ghost<IndexVec<u32, I>>, ts: Ghost<Seq<Int>>, k: usize, n: usize) {
    l4_all(s, k);
    weight_at_le(ts, s, k, n);
}

// The fail twin of the weights root sets this cfg: `weight_at_le` with its proof unchanged and
// without the bound on how often an index occurs that it needs, under which an index counted twice can exceed the sum.
#[cfg(thrust_weights_fail)]
#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|j: Int| !(0 <= j && j < k) || I::index_logic(s[j]) < n))]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < n) || 0 <= ts[x]))]
#[thrust_macros::ensures(weight_at::<I>(ts, s, k) <= weight_first(ts, n))]
pub fn weight_at_le_repeated<I: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, s: Ghost<IndexVec<u32, I>>, k: usize, n: usize) {
    weight_l5(ts, s, k, n);
    weight_all_below(ts, s, k, n);
}
