//! The counting lemmas of stage 7 (README.md of the stage files): the permutation split of
//! `layout()`'s memory order. The counts are recursive logic functions over the model of an
//! `IndexVec<u32, I>`, read through `Idx::index_logic`; the lemmas prove them by induction, and
//! `permutation_split` gives that of `n` distinct indices at least `n - b` are at least `b`.

use crate::thrust_models;
use thrust_models::model::{Int, UInt};
use thrust_models::{forall, Ghost};

use crate::case_study::USize;
use crate::rustc_index::{Idx, IndexVec};

/// The entries among the first `k` of `s` whose index is `x`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn occ<I: Idx + thrust_models::Model<Ty: PartialEq>>(x: USize, s: IndexVec<u32, I>, k: USize) -> USize {
    if k <= 0 {
        0
    } else {
        occ::<I>(x, s, k - 1) + if I::index_logic(s[k - 1]) == x { 1 } else { 0 }
    }
}

/// The entries among the first `k` of `s` whose index is below `b`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn cnt_lt<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: IndexVec<u32, I>, k: USize, b: USize) -> USize {
    if k <= 0 {
        0
    } else {
        cnt_lt::<I>(s, k - 1, b) + if I::index_logic(s[k - 1]) < b { 1 } else { 0 }
    }
}

/// The entries among the first `k` of `s` whose index is at least `b`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn cnt_ge<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: IndexVec<u32, I>, k: USize, b: USize) -> USize {
    if k <= 0 {
        0
    } else {
        cnt_ge::<I>(s, k - 1, b) + if I::index_logic(s[k - 1]) >= b { 1 } else { 0 }
    }
}

/// The first `k` entries of `s` have distinct indices.
#[thrust_macros::predicate]
pub fn distinct<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: IndexVec<u32, I>, k: USize) -> bool {
    forall(|i: Int, j: Int| {
        !(0 <= i && i < j && j < k) || I::index_logic(s[i]) != I::index_logic(s[j])
    })
}

/// L3: an index bound one higher counts the entries at the bound as well.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(cnt_lt::<I>(s, k, b + 1) == cnt_lt::<I>(s, k, b) + occ::<I>(b, s, k))]
pub fn l3<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: Ghost<IndexVec<u32, I>>, k: usize, b: usize) {
    if k > 0 {
        l3(s, k - 1, b);
    }
}

/// The index of entry `k` does not occur among the first `j <= k` when the first `k + 1` are
/// distinct.
#[thrust_macros::lemma]
#[thrust_macros::variant(j)]
#[thrust_macros::requires(j <= k && distinct::<I>(s, k + 1))]
#[thrust_macros::ensures(occ::<I>(I::index_logic(s[k]), s, j) == 0)]
pub fn absent<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: Ghost<IndexVec<u32, I>>, k: usize, j: usize) {
    if j > 0 {
        absent(s, k, j - 1);
    }
}

/// L4 for every index: distinct entries hold each index at most once.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(distinct::<I>(s, k))]
#[thrust_macros::ensures(forall(|x: UInt| occ::<I>(x, s, k) <= 1))]
pub fn l4_all<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: Ghost<IndexVec<u32, I>>, k: usize) {
    if k > 0 {
        l4_all(s, k - 1);
        absent(s, k - 1, k - 1);
    }
}

/// L4 for one index.
#[thrust_macros::lemma]
#[thrust_macros::requires(distinct::<I>(s, k))]
#[thrust_macros::ensures(occ::<I>(x, s, k) <= 1)]
pub fn l4<I: Idx + thrust_models::Model<Ty: PartialEq>>(x: usize, s: Ghost<IndexVec<u32, I>>, k: usize) {
    l4_all(s, k);
}

/// No index is below 0.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(b == 0)]
#[thrust_macros::ensures(cnt_lt::<I>(s, k, b) == 0)]
pub fn l0<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: Ghost<IndexVec<u32, I>>, k: usize, b: usize) {
    if k > 0 {
        l0(s, k - 1, b);
    }
}

/// L5, the pigeonhole bound: when every index below `b` occurs at most once, at most `b`
/// entries are below `b`.
#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::requires(forall(|x: UInt| !(x < b) || occ::<I>(x, s, n) <= 1))]
#[thrust_macros::ensures(cnt_lt::<I>(s, n, b) <= b)]
pub fn l5<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: Ghost<IndexVec<u32, I>>, n: usize, b: usize) {
    if b > 0 {
        l5(s, n, b - 1);
        l3(s, n, b - 1);
    } else {
        l0(s, n, b);
    }
}

/// L6: every entry is below `b` or at least `b`.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(cnt_lt::<I>(s, k, b) + cnt_ge::<I>(s, k, b) == k)]
pub fn l6<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: Ghost<IndexVec<u32, I>>, k: usize, b: usize) {
    if k > 0 {
        l6(s, k - 1, b);
    }
}

/// The permutation split: of `n` distinct indices, at least `n - b` are at least `b`.
#[thrust_macros::lemma]
#[thrust_macros::requires(b <= n && distinct::<I>(s, n))]
#[thrust_macros::ensures(cnt_ge::<I>(s, n, b) >= n - b)]
pub fn permutation_split<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: Ghost<IndexVec<u32, I>>, n: usize, b: usize) {
    l4_all(s, n);
    l5(s, n, b);
    l6(s, n, b);
}

/// `distinct` from injectivity stated by `index_is`, as univariant's `arbitrary_of` states it.
#[thrust_macros::lemma]
#[thrust_macros::requires(
    forall(|k: USize, k2: USize, i: USize|
        !(0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2) && <I as Idx>::index_is(s[k], i))
            || !<I as Idx>::index_is(s[k2], i))
)]
#[thrust_macros::ensures(distinct::<I>(s, n))]
pub fn distinct_of_injective<I: Idx + thrust_models::Model<Ty: PartialEq>>(s: Ghost<IndexVec<u32, I>>, n: usize) {
}
