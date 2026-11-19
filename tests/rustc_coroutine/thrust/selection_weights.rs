//! The weight of a selection of entries of an index list, `vf[f[0]], vf[f[1]], ...` (as `counts`'s
//! `selection_of` gives the entries of a variant that are Assigned to it), and the bound that two
//! selections with no index in common weigh at most the first `n` entries of the weights `ts`,
//! none of which is negative. The sums are recursive logic functions over the first `m` positions
//! of the selection, read through `Idx::index_logic` as in `weights`, and the lemmas prove them by
//! induction. Each lemma is stated for every `ts`, `vf` and `f` (a selection is not a program
//! value, so no lemma can take it as a parameter), with the positions and bounds as parameters.

use crate::thrust_models;
use thrust_models::model::{Array, Int, Seq};
use thrust_models::{exists, forall};

use crate::case_study::counts::{acc_cnt, selects};
use crate::case_study::lemmas::occ;
use crate::case_study::weights::{weight_all_below, weight_below, weight_first, weight_at, weight_l0, weight_l3, weight_of_le};
use thrust_models::Ghost;
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

/// The weighted L5 for a selection and a list: when every index below `b` occurs at most once in
/// the two together, their entries below `b` weigh at most the first `b` entries of `ts`.
#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < b) || 0 <= ts[x]))]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>|
    !(forall(|x: USize| x < b ==> occ_sel::<J, L>(x, vf, f, m) + occ::<L>(x, p, c) <= 1))
        || wbelow_sel::<J, L>(ts, vf, f, m, b) + weight_below::<L>(ts, p, c, b) <= weight_first(ts, b)))]
pub fn l5_sel_list<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(
    ts: Ghost<Seq<Int>>,
    p: Ghost<IndexVec<u32, L>>,
    c: usize,
    m: usize,
    b: usize,
) {
    if b > 0 {
        l5_sel_list::<J, L>(ts, p, c, m, b - 1);
        l3_sel::<J, L>(m, b - 1);
        weight_l3(ts, p, c, b - 1);
        of_sel::<J, L>(m, b - 1);
        weight_of_le(ts, p, c, b - 1);
    } else {
        l0_sel::<J, L>(m, b);
        weight_l0(ts, p, c, b);
    }
}

/// A selection and a list whose indices are below `n` and that together hold no index twice weigh
/// at most the first `n` entries of `ts`, none of which is negative.
#[thrust_macros::lemma]
#[thrust_macros::requires(forall(|j: Int| !(0 <= j && j < c) || L::index_logic(p[j]) < n))]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < n) || 0 <= ts[x]))]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>|
    !(forall(|x: USize| occ_sel::<J, L>(x, vf, f, m) + occ::<L>(x, p, c) <= 1)
        && forall(|j: Int| !(0 <= j && j < m) || L::index_logic(vf[f[j]]) < n))
        || wat_sel::<J, L>(ts, vf, f, m) + weight_at::<L>(ts, p, c) <= weight_first(ts, n)))]
pub fn sel_list_le<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(
    ts: Ghost<Seq<Int>>,
    p: Ghost<IndexVec<u32, L>>,
    c: usize,
    m: usize,
    n: usize,
) {
    l5_sel_list::<J, L>(ts, p, c, m, n);
    all_below_sel::<J, L>(m, n);
    weight_all_below(ts, p, c, n);
}

/// An index no position of the selection has occurs in none.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, x: USize|
    !(forall(|j: Int| !(0 <= j && j < k) || L::index_logic(vf[f[j]]) != x))
        || occ_sel::<J, L>(x, vf, f, k) == 0))]
pub fn occ_sel_zero<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(k: usize) {
    if k > 0 {
        occ_sel_zero::<J, L>(k - 1);
    }
}

/// An index that occurs in the selection is the index of one of its positions.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, x: USize|
    !(occ_sel::<J, L>(x, vf, f, k) > 0)
        || exists(|j: Int| 0 <= j && j < k && L::index_logic(vf[f[j]]) == x)))]
pub fn occ_sel_pos<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(k: usize) {
    occ_sel_zero::<J, L>(k);
}

/// The first `m` positions of `f` select entries of the class `e` of `a` from `vf`, at increasing
/// positions (`selects` of `counts`), and `vf` holds no local of that class twice (the property of
/// the locals Assigned to a variant that eligibility gives).
#[thrust_macros::predicate]
#[thrust::opaque]
pub fn sel_ok<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    vf: IndexVec<J, L>,
    f: Array<Int, Int>,
    a: IndexVec<K, T>,
    e: T,
    m: USize,
) -> bool {
    forall(|i: Int, j: Int| !(0 <= i && i < j && j < m) || f[i] < f[j])
        && forall(|j: Int| !(0 <= j && j < m) || (0 <= f[j] && f[j] < vf.len() && a[L::index_logic(vf[f[j]])] == e))
        && forall(|p: Int, q: Int|
            !(0 <= p && p < vf.len() && 0 <= q && q < vf.len()
                && L::index_logic(vf[p]) == L::index_logic(vf[q]) && a[L::index_logic(vf[p])] == e)
                || p == q)
}

/// `sel_ok` of fewer positions.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty|
    !(0 < m && sel_ok::<J, L, K, T>(vf, f, a, e, m)) || sel_ok::<J, L, K, T>(vf, f, a, e, m - 1)))]
#[thrust::reveal(sel_ok)]
pub fn sel_ok_prefix<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(m: usize) {
}

/// The positions of a `sel_ok` selection have different indices.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty, i: Int, j: Int|
    !(sel_ok::<J, L, K, T>(vf, f, a, e, m) && 0 <= i && i < j && j < m)
        || !(L::index_logic(vf[f[i]]) == L::index_logic(vf[f[j]]))))]
#[thrust::reveal(sel_ok)]
pub fn sel_positions_differ<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(m: usize) {
}

/// The index of the last position of a `sel_ok` selection occurs in none before it.
#[thrust_macros::lemma]
#[thrust_macros::requires(0 < m)]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty|
    !sel_ok::<J, L, K, T>(vf, f, a, e, m)
        || occ_sel::<J, L>(L::index_logic(vf[f[m - 1]]), vf, f, m - 1) == 0))]
pub fn occ_before_last<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(m: usize) {
    sel_positions_differ::<J, L, K, T>(m);
    occ_sel_zero::<J, L>(m - 1);
}

/// The unfolding of `occ_sel` at one more position.
#[thrust_macros::lemma]
#[thrust_macros::requires(0 < m)]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, x: USize|
    occ_sel::<J, L>(x, vf, f, m)
        == occ_sel::<J, L>(x, vf, f, m - 1) + if L::index_logic(vf[f[m - 1]]) == x { 1 } else { 0 }))]
pub fn occ_sel_step<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(m: usize) {
}

/// A `sel_ok` selection holds no index twice.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty, x: USize|
    !sel_ok::<J, L, K, T>(vf, f, a, e, m) || occ_sel::<J, L>(x, vf, f, m) <= 1))]
pub fn occ_sel_once<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(m: usize) {
    if m > 0 {
        sel_ok_prefix::<J, L, K, T>(m);
        occ_sel_once::<J, L, K, T>(m - 1);
        occ_before_last::<J, L, K, T>(m);
        occ_sel_step::<J, L>(m);
    }
}

/// An index that occurs in a `sel_ok` selection is of its class.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty, x: USize|
    !(sel_ok::<J, L, K, T>(vf, f, a, e, k) && occ_sel::<J, L>(x, vf, f, k) > 0)
        || a[x] == e))]
#[thrust::reveal(sel_ok)]
pub fn occ_sel_class<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(k: usize) {
    occ_sel_pos::<J, L>(k);
}

/// An index that occurs in a list none of whose entries is of one class of `a` is not of that class.
#[thrust_macros::lemma]
#[thrust_macros::variant(c)]
#[thrust_macros::ensures(forall(|p: Seq<<L as thrust_models::Model>::Ty>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty, x: USize|
    !(forall(|j: Int| !(0 <= j && j < c) || !(a[L::index_logic(p[j])] == e))
        && occ::<L>(x, p, c) > 0)
        || !(a[x] == e)))]
pub fn occ_list_class<L: Idx + thrust_models::Model, T: thrust_models::Model>(c: usize) {
    if c > 0 {
        occ_list_class::<L, T>(c - 1);
    }
}

/// A `sel_ok` selection and a list of distinct indices none of which is of its class hold no index
/// twice in the two together.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty,
        p: Seq<<L as thrust_models::Model>::Ty>, x: USize|
    !(sel_ok::<J, L, K, T>(vf, f, a, e, m)
        && forall(|j: Int| !(0 <= j && j < c) || !(a[L::index_logic(p[j])] == e))
        && occ::<L>(x, p, c) <= 1)
        || occ_sel::<J, L>(x, vf, f, m) + occ::<L>(x, p, c) <= 1))]
pub fn sel_list_disjoint<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(m: usize, c: usize) {
    occ_sel_once::<J, L, K, T>(m);
    occ_sel_class::<J, L, K, T>(m);
    occ_list_class::<L, T>(c);
}

/// There are at most `k` entries of one class among the first `k` entries of a list.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(forall(|fields: Seq<<L as thrust_models::Model>::Ty>, a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty|
    acc_cnt::<J, L, K, T>(fields, a, e, k) <= k))]
pub fn acc_cnt_le<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(k: usize) {
    if k > 0 {
        acc_cnt_le::<J, L, K, T>(k - 1);
    }
}

/// `sel_list_le` for every position count up to `k`.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|j: Int| !(0 <= j && j < c) || L::index_logic(p[j]) < n))]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < n) || 0 <= ts[x]))]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, m: USize|
    !(m <= k
        && forall(|x: USize| occ_sel::<J, L>(x, vf, f, m) + occ::<L>(x, p, c) <= 1)
        && forall(|j: Int| !(0 <= j && j < m) || L::index_logic(vf[f[j]]) < n))
        || wat_sel::<J, L>(ts, vf, f, m) + weight_at::<L>(ts, p, c) <= weight_first(ts, n)))]
pub fn sel_list_le_upto<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(
    ts: Ghost<Seq<Int>>,
    p: Ghost<IndexVec<u32, L>>,
    c: usize,
    n: usize,
    k: usize,
) {
    if k > 0 {
        sel_list_le_upto::<J, L>(ts, p, c, n, k - 1);
    }
    sel_list_le::<J, L>(ts, p, c, k, n);
}

/// `sel_list_disjoint` for every position count up to `k`.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty,
        p: Seq<<L as thrust_models::Model>::Ty>, m: USize, x: USize|
    !(m <= k
        && sel_ok::<J, L, K, T>(vf, f, a, e, m)
        && forall(|j: Int| !(0 <= j && j < c) || !(a[L::index_logic(p[j])] == e))
        && occ::<L>(x, p, c) <= 1)
        || occ_sel::<J, L>(x, vf, f, m) + occ::<L>(x, p, c) <= 1))]
pub fn sel_list_disjoint_upto<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(c: usize, k: usize) {
    if k > 0 {
        sel_list_disjoint_upto::<J, L, K, T>(c, k - 1);
    }
    sel_list_disjoint::<J, L, K, T>(k, c);
}

/// `sel_ok` from `selects` (`counts`) of the entries of class `e` of `vf`, and the property that
/// `vf` holds no local of that class twice.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>,
        a: Seq<<T as thrust_models::Model>::Ty>, e: <T as thrust_models::Model>::Ty, m: Int, mu: USize|
    !(m == mu && selects::<J, L, K, T>(vf, a, e, f, m, vf.len())
        && forall(|p: Int, q: Int|
            !(0 <= p && p < vf.len() && 0 <= q && q < vf.len()
                && L::index_logic(vf[p]) == L::index_logic(vf[q]) && a[L::index_logic(vf[p])] == e)
                || p == q))
        || sel_ok::<J, L, K, T>(vf, f, a, e, mu)))]
#[thrust::reveal(selects, sel_ok)]
pub fn sel_ok_intro<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>() {
}

/// A selection's weights are not negative when none is.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < n) || 0 <= ts[x]))]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, m: USize|
    !(m <= k && forall(|j: Int| !(0 <= j && j < m) || L::index_logic(vf[f[j]]) < n))
        || 0 <= wat_sel::<J, L>(ts, vf, f, m)))]
pub fn wat_sel_nonneg_upto<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, n: usize, k: usize) {
    if k > 0 {
        wat_sel_nonneg_upto::<J, L>(ts, n, k - 1);
    }
    wat_sel_nonneg::<J, L>(ts, n, k);
}

/// The weights at the first `m` positions of a selection whose indices are below `n` are not
/// negative when none is.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < n) || 0 <= ts[x]))]
#[thrust_macros::ensures(forall(|vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>|
    !(forall(|j: Int| !(0 <= j && j < m) || L::index_logic(vf[f[j]]) < n))
        || 0 <= wat_sel::<J, L>(ts, vf, f, m)))]
pub fn wat_sel_nonneg<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(ts: Ghost<Seq<Int>>, n: usize, m: usize) {
    if m > 0 {
        wat_sel_nonneg::<J, L>(ts, n, m - 1);
    }
}

// The fail twin of the selection_weights root sets this cfg: `l3_sel` with its proof unchanged and a
// sum one too large, refuted.
#[cfg(thrust_selection_weights_fail)]
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::ensures(forall(|ts: Seq<Int>, vf: Seq<<L as thrust_models::Model>::Ty>, f: Array<Int, Int>|
    wbelow_sel::<J, L>(ts, vf, f, m, b + 1) == wbelow_sel::<J, L>(ts, vf, f, m, b) + wof_sel::<J, L>(ts, vf, f, m, b) + 1))]
pub fn l3_sel_off_by_one<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(m: usize, b: usize) {
    if m > 0 {
        l3_sel_off_by_one::<J, L>(m - 1, b);
    }
}
