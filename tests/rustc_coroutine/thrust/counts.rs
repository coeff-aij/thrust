//! The count of a variant's fields in stage 7 (sites 1 and 3 of layout()'s per-variant closure):
//! the items a `Map` over a `Filter` of a variant's field list yields are no more than the locals
//! of the class the filter accepts. The counts are recursive logic functions over positions, read
//! through `Idx::index_logic` as in `lemmas`, and the lemmas prove them by induction: the
//! pigeonhole bound L5 over the field list's entries of the class (`acc_bound`), and the bound of
//! Creusot's index map of `Filter` by those entries (`map_bound`). `filter_count` joins them at
//! the witnesses of `Map::produces`.

use crate::thrust_models;
use thrust_models::model::{Array, Int, Seq};
use thrust_models::forall;

use crate::case_study::iter::{Filter, Map};
use crate::case_study::USize;
use crate::rustc_index::{Idx, IndexVec, SliceIter};
use crate::IteratorSpec;

/// The locals below `k` whose class in `a` is `e`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn class_cnt<K: Idx + thrust_models::Model, T: thrust_models::Model>(a: IndexVec<K, T>, k: USize, e: T) -> USize {
    if k <= 0 {
        0
    } else {
        class_cnt::<K, T>(a, k - 1, e) + if a[k - 1] == e { 1 } else { 0 }
    }
}

/// The entries among the first `k` of `fields` whose local is of class `e`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn acc_cnt<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: IndexVec<J, L>,
    a: IndexVec<K, T>,
    e: T,
    k: USize,
) -> USize {
    if k <= 0 {
        0
    } else {
        acc_cnt::<J, L, K, T>(fields, a, e, k - 1) + if a[L::index_logic(fields[k - 1])] == e { 1 } else { 0 }
    }
}

/// The entries among the first `k` of `fields` whose local is of class `e` and below `b`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn acc_lt<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: IndexVec<J, L>,
    a: IndexVec<K, T>,
    e: T,
    k: USize,
    b: USize,
) -> USize {
    if k <= 0 {
        0
    } else {
        acc_lt::<J, L, K, T>(fields, a, e, k - 1, b)
            + if a[L::index_logic(fields[k - 1])] == e && L::index_logic(fields[k - 1]) < b { 1 } else { 0 }
    }
}

/// The entries among the first `k` of `fields` whose local is `x`, of class `e`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn acc_occ<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    x: USize,
    fields: IndexVec<J, L>,
    a: IndexVec<K, T>,
    e: T,
    k: USize,
) -> USize {
    if k <= 0 {
        0
    } else {
        acc_occ::<J, L, K, T>(x, fields, a, e, k - 1)
            + if a[L::index_logic(fields[k - 1])] == e && L::index_logic(fields[k - 1]) == x { 1 } else { 0 }
    }
}

/// No two of the first `k` entries of `fields` name the same local of class `e` (eligibility's
/// property 2c for a variant's field list).
#[thrust_macros::predicate]
pub fn acc_distinct<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: IndexVec<J, L>,
    a: IndexVec<K, T>,
    e: T,
    k: USize,
) -> bool {
    forall(|p: Int, q: Int| {
        !(0 <= p && p < q && q < k
            && L::index_logic(fields[p]) == L::index_logic(fields[q])
            && a[L::index_logic(fields[p])] == e)
    })
}

/// L3 of `lemmas` over the entries of class `e`.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(acc_lt::<J, L, K, T>(*fields, *a, *e, k, b + 1)
    == acc_lt::<J, L, K, T>(*fields, *a, *e, k, b) + acc_occ::<J, L, K, T>(b, *fields, *a, *e, k))]
pub fn acc_l3<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize, b: usize,
) {
    if k > 0 {
        acc_l3(fields, a, e, k - 1, b);
    }
}

/// The local of entry `k` does not occur, of class `e`, among the first `j <= k`.
#[thrust_macros::lemma]
#[thrust_macros::variant(j)]
#[thrust_macros::requires(j <= k && acc_distinct::<J, L, K, T>(*fields, *a, *e, k + 1))]
#[thrust_macros::ensures(acc_occ::<J, L, K, T>(L::index_logic((*fields)[k]), *fields, *a, *e, j) == 0)]
pub fn acc_absent<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize, j: usize,
) {
    if j > 0 {
        acc_absent(fields, a, e, k, j - 1);
    }
}

/// L4 of `lemmas` over the entries of class `e`: each local occurs at most once among them.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(acc_distinct::<J, L, K, T>(*fields, *a, *e, k))]
#[thrust_macros::ensures(forall(|x: USize| acc_occ::<J, L, K, T>(x, *fields, *a, *e, k) <= 1))]
pub fn acc_l4_all<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize,
) {
    if k > 0 {
        acc_l4_all(fields, a, e, k - 1);
        acc_absent(fields, a, e, k - 1, k - 1);
    }
}

/// A local not of class `e` occurs among no entry of class `e`.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(forall(|x: USize| (*a)[x] == *e || acc_occ::<J, L, K, T>(x, *fields, *a, *e, k) == 0))]
pub fn acc_zero<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize,
) {
    if k > 0 {
        acc_zero(fields, a, e, k - 1);
    }
}

/// No local is below 0.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(b == 0)]
#[thrust_macros::ensures(acc_lt::<J, L, K, T>(*fields, *a, *e, k, b) == 0)]
pub fn acc_l0<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize, b: usize,
) {
    if k > 0 {
        acc_l0(fields, a, e, k - 1, b);
    }
}

/// L5 of `lemmas` over the entries of class `e`: when each local below `b` occurs at most once among them,
/// they name no more locals below `b` than there are of class `e`.
#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::requires(forall(|x: USize| !(x < b) || acc_occ::<J, L, K, T>(x, *fields, *a, *e, k) <= 1))]
#[thrust_macros::ensures(acc_lt::<J, L, K, T>(*fields, *a, *e, k, b) <= class_cnt::<K, T>(*a, b, *e))]
pub fn acc_l5<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize, b: usize,
) {
    if b > 0 {
        acc_l5(fields, a, e, k, b - 1);
        acc_l3(fields, a, e, k, b - 1);
        acc_zero(fields, a, e, k);
    } else {
        acc_l0(fields, a, e, k, b);
    }
}

/// When every entry's local is below `n`, the entries of class `e` below `n` are all of them.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|p: Int| !(0 <= p && p < k) || L::index_logic((*fields)[p]) < n))]
#[thrust_macros::ensures(acc_lt::<J, L, K, T>(*fields, *a, *e, k, n) == acc_cnt::<J, L, K, T>(*fields, *a, *e, k))]
pub fn acc_all<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize, n: usize,
) {
    if k > 0 {
        acc_all(fields, a, e, k - 1, n);
    }
}

/// The entries of class `e` are no more than the locals of class `e`.
#[thrust_macros::lemma]
#[thrust_macros::requires(acc_distinct::<J, L, K, T>(*fields, *a, *e, k))]
#[thrust_macros::requires(forall(|p: Int| !(0 <= p && p < k) || L::index_logic((*fields)[p]) < n))]
#[thrust_macros::ensures(acc_cnt::<J, L, K, T>(*fields, *a, *e, k) <= class_cnt::<K, T>(*a, n, *e))]
pub fn acc_bound<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize, n: usize,
) {
    acc_l4_all(fields, a, e, k);
    acc_l5(fields, a, e, k, n);
    acc_all(fields, a, e, k, n);
}

/// `f` maps the first `m` positions, increasingly, to entries of `fields` below `k` of class
/// `e` (Creusot's index map of `Filter`).
#[thrust_macros::predicate]
pub fn selects<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: IndexVec<J, L>,
    a: IndexVec<K, T>,
    e: T,
    f: Array<Int, Int>,
    m: Int,
    k: USize,
) -> bool {
    0 <= m
        && forall(|j: Int| !(0 <= j && j < m) || (0 <= f[j] && f[j] < k && a[L::index_logic(fields[f[j]])] == e))
        && forall(|i: Int, j: Int| !(0 <= i && i < j && j < m) || f[i] < f[j])
}

/// A selection below `k + 1` is one below `k`, less its last position when that is `k`, which
/// is then an entry of class `e`.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !(selects::<J, L, K, T>(*fields, *a, *e, f, m, k + 1) && 0 < m && f[m - 1] == k)
        || (selects::<J, L, K, T>(*fields, *a, *e, f, m - 1, k) && (*a)[L::index_logic((*fields)[k])] == *e)))]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !(selects::<J, L, K, T>(*fields, *a, *e, f, m, k + 1) && !(0 < m && f[m - 1] == k))
        || selects::<J, L, K, T>(*fields, *a, *e, f, m, k)))]
pub fn selects_step<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize,
) {
}

/// A selection below `k` has no more positions than there are entries of class `e` below `k`.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !selects::<J, L, K, T>(*fields, *a, *e, f, m, k) || m <= acc_cnt::<J, L, K, T>(*fields, *a, *e, k)))]
pub fn map_bound<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize,
) {
    if k > 0 {
        map_bound(fields, a, e, k - 1);
        selects_step(fields, a, e, k - 1);
    }
}

/// The items a `Map` over a `Filter` of `fields` yields are no more than the locals of class
/// `e` in `a`, when the filter accepts the entries whose local is of class `e`, the entries of
/// class `e` name distinct locals, and every entry names a local of `a`; `k` and `n` are the two
/// lengths, which a lemma's proof cannot call `len` for. The witnesses are
/// universally quantified, so the caller instantiates them with those of `collect`'s
/// postcondition.
#[thrust_macros::context]
// `inv` states the `pre!` of the two closures, which the call hands over.
#[thrust_macros::requires(<Map<Filter<SliceIter<'a, L>, P>, M> as IteratorSpec>::inv(*it))]
#[thrust_macros::requires(*(*it).0.0.0 == *fields && (*it).0.0.1 == 0 && k == (*fields).len() && n == (*a).len())]
#[thrust_macros::requires(forall(|p: Int| !(0 <= p && p < (*fields).len()) || L::index_logic((*fields)[p]) < (*a).len()))]
#[thrust_macros::requires(acc_distinct::<J, L, K, T>(*fields, *a, *e, (*fields).len()))]
#[thrust_macros::requires(forall(|s: Seq<&<L as thrust_models::Model>::Ty>, k: Int, r: bool|
    !(0 <= k && k < s.len() && Filter::<SliceIter<'a, L>, P>::answers((*it).0.1, s, k, r))
        || r == ((*a)[L::index_logic(*s[k])] == *e)))]
#[thrust_macros::ensures(forall(|v: Seq<<B as thrust_models::Model>::Ty>, mid: <Map<Filter<SliceIter<'a, L>, P>, M> as thrust_models::Model>::Ty|
    !<Map<Filter<SliceIter<'a, L>, P>, M> as IteratorSpec>::produces(*it, v, mid)
        || v.len() <= class_cnt::<K, T>(*a, (*a).len(), *e)))]
#[thrust_macros::lemma]
pub fn filter_count<'a, J, L, K, T, P, M, B>(
    it: &Map<Filter<SliceIter<'a, L>, P>, M>,
    fields: &'a IndexVec<J, L>,
    a: &IndexVec<K, T>,
    e: &T,
    k: usize,
    n: usize,
) where
    J: Idx + thrust_models::Model,
    L: Idx + thrust_models::Model,
    K: Idx + thrust_models::Model,
    T: thrust_models::Model,
    P: Fn(&&'a L) -> bool,
    M: FnMut(&'a L) -> B,
    B: thrust_models::Model,
{
    map_bound(fields, a, e, k);
    acc_bound(fields, a, e, k, n);
}
