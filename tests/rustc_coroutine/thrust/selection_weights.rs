//! The weight of a selection of entries of an index list, `vf[f[0]], vf[f[1]], ...` (as `counts`'s
//! `selection_of` gives the entries of a variant that are Assigned to it), and the bound that two
//! selections with no index in common weigh at most the first `n` entries of the weights `ts`,
//! none of which is negative. The sums are recursive logic functions over the first `m` positions
//! of the selection, read through `Idx::index_logic` as in `weights`, and the lemmas prove them by
//! induction. Each lemma is stated for every `ts`, `vf` and `f` (a selection is not a program
//! value, so no lemma can take it as a parameter), with the positions and bounds as parameters.

use crate::thrust_models;
use thrust_models::model::{Array, Int, Seq};
use thrust_models::forall;

use crate::case_study::weights::weight_first;
use crate::case_study::USize;
use crate::rustc_index::{Idx, IndexVec};

/// The positions among the first `m` of the selection whose index is `x`.
#[thrust_macros::logic]
#[thrust_macros::variant(m)]
pub fn occ_sel<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(x: USize, vf: IndexVec<J, L>, f: Array<Int, Int>, m: USize) -> USize {
    if m <= 0 {
        0
    } else {
        occ_sel::<J, L>(x, vf, f, m - 1) + if L::index_logic(vf[f[m - 1]]) == x { 1 } else { 0 }
    }
}

/// The sum of the entries of `ts` at the indices of the first `m` selected positions.
#[thrust_macros::logic]
#[thrust_macros::variant(m)]
pub fn wat_sel<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(ts: Seq<Int>, vf: IndexVec<J, L>, f: Array<Int, Int>, m: USize) -> Int {
    if m <= 0 {
        0
    } else {
        wat_sel::<J, L>(ts, vf, f, m - 1) + ts[L::index_logic(vf[f[m - 1]])]
    }
}

/// As `wat_sel`, over the positions whose index is below `b`.
#[thrust_macros::logic]
#[thrust_macros::variant(m)]
pub fn wbelow_sel<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(ts: Seq<Int>, vf: IndexVec<J, L>, f: Array<Int, Int>, m: USize, b: USize) -> Int {
    if m <= 0 {
        0
    } else if L::index_logic(vf[f[m - 1]]) < b {
        wbelow_sel::<J, L>(ts, vf, f, m - 1, b) + ts[L::index_logic(vf[f[m - 1]])]
    } else {
        wbelow_sel::<J, L>(ts, vf, f, m - 1, b)
    }
}

/// As `wat_sel`, over the positions whose index is `x`.
#[thrust_macros::logic]
#[thrust_macros::variant(m)]
pub fn wof_sel<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(ts: Seq<Int>, vf: IndexVec<J, L>, f: Array<Int, Int>, m: USize, x: USize) -> Int {
    if m <= 0 {
        0
    } else if L::index_logic(vf[f[m - 1]]) == x {
        wof_sel::<J, L>(ts, vf, f, m - 1, x) + ts[x]
    } else {
        wof_sel::<J, L>(ts, vf, f, m - 1, x)
    }
}

/// A bound one higher adds the weight of the positions at the bound.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>|
    wbelow_sel::<J, L>(ts, vf, f, m, b + 1) == wbelow_sel::<J, L>(ts, vf, f, m, b) + wof_sel::<J, L>(ts, vf, f, m, b)))]
pub fn l3_sel<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(m: usize, b: usize) {
    if m > 0 {
        l3_sel::<J, L>(m - 1, b);
    }
}

/// No position is below 0.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::requires(b == 0)]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>|
    wbelow_sel::<J, L>(ts, vf, f, m, b) == 0))]
pub fn l0_sel<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(m: usize, b: usize) {
    if m > 0 {
        l0_sel::<J, L>(m - 1, b);
    }
}

/// An index no position has gets no weight, and one with at most one position gets at most its own.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>|
    !(0 <= ts[x])
        || ((occ_sel::<J, L>(x, vf, f, m) != 0 || wof_sel::<J, L>(ts, vf, f, m, x) == 0)
            && (occ_sel::<J, L>(x, vf, f, m) > 1 || wof_sel::<J, L>(ts, vf, f, m, x) <= ts[x]))))]
pub fn of_sel<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(m: usize, x: usize) {
    if m > 0 {
        of_sel::<J, L>(m - 1, x);
    }
}

/// The weighted L5 for two selections: when every index below `b` occurs at most once in the two
/// together, their positions below `b` weigh at most the first `b` entries of `ts`.
#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, vg: Seq<<L as thrust_models::Model>::Ty>, g: Array<Int, Int>|
    !(forall(|x: USize| x < b ==> occ_sel::<J, L>(x, vf, f, m) + occ_sel::<J, L>(x, vg, g, n) <= 1)
        && forall(|x: Int| !(0 <= x && x < b) || 0 <= ts[x]))
        || wbelow_sel::<J, L>(ts, vf, f, m, b) + wbelow_sel::<J, L>(ts, vg, g, n, b) <= weight_first(ts, b)))]
pub fn l5_sel_two<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(m: usize, n: usize, b: usize) {
    if b > 0 {
        l5_sel_two::<J, L>(m, n, b - 1);
        l3_sel::<J, L>(m, b - 1);
        l3_sel::<J, L>(n, b - 1);
        of_sel::<J, L>(m, b - 1);
        of_sel::<J, L>(n, b - 1);
    } else {
        l0_sel::<J, L>(m, b);
        l0_sel::<J, L>(n, b);
    }
}

/// Positions all below `n` are all counted below `n`.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>|
    !(forall(|j: Int| !(0 <= j && j < m) || L::index_logic(vf[f[j]]) < n))
        || wbelow_sel::<J, L>(ts, vf, f, m, n) == wat_sel::<J, L>(ts, vf, f, m)))]
pub fn all_below_sel<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(m: usize, n: usize) {
    if m > 0 {
        all_below_sel::<J, L>(m - 1, n);
    }
}

/// Two selections whose indices are below `n` and that together hold no index twice weigh at most
/// the first `n` entries of `ts`, none of which is negative.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, vg: Seq<<L as thrust_models::Model>::Ty>, g: Array<Int, Int>|
    !(forall(|x: USize| occ_sel::<J, L>(x, vf, f, m) + occ_sel::<J, L>(x, vg, g, k) <= 1)
        && forall(|j: Int| !(0 <= j && j < m) || L::index_logic(vf[f[j]]) < n)
        && forall(|j: Int| !(0 <= j && j < k) || L::index_logic(vg[g[j]]) < n)
        && forall(|x: Int| !(0 <= x && x < n) || 0 <= ts[x]))
        || wat_sel::<J, L>(ts, vf, f, m) + wat_sel::<J, L>(ts, vg, g, k) <= weight_first(ts, n)))]
pub fn sel_two_le<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(m: usize, k: usize, n: usize) {
    l5_sel_two::<J, L>(m, k, n);
    all_below_sel::<J, L>(m, n);
    all_below_sel::<J, L>(k, n);
}
