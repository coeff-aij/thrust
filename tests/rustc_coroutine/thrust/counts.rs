//! The count of a variant's fields in stage 7 (sites 1 and 3 of layout()'s per-variant closure):
//! the items a `Map` over a `Filter` of a variant's field list yields are no more than the locals
//! of the class the filter accepts. The counts are recursive logic functions over positions, read
//! through `Idx::index_logic` as in `lemmas`, and the lemmas prove them by induction: the
//! pigeonhole bound L5 over the field list's entries of the class (`acc_bound`), and the bound of
//! Creusot's index map of `Filter` by those entries (`map_bound`). `filter_count` joins them at
//! the witnesses of `Map::produces`. The weighted forms bound the weight of the selected
//! locals (site 4) in the same way.

use crate::thrust_models;
use thrust_models::model::{Array, Closure, Int, Mut, Seq};
use thrust_models::{exists, forall};

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
/// `e` (Creusot's index map of `Filter`). Opaque: the lemmas that build or read a selection reveal
/// it, the others pass it on as an atom.
#[thrust_macros::predicate]
#[thrust::opaque]
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
#[thrust::reveal(selects)]
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
    } else {
        selects_base(fields, a, e);
    }
}

/// A selection below 0 has no positions.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>, z: USize|
    !(z == 0 && selects::<J, L, K, T>(*fields, *a, *e, f, m, z)) || m == 0))]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>, z: USize|
    !(z == 0 && selects_all::<J, L, K, T>(*fields, *a, *e, f, m, z)) || m == 0))]
#[thrust::reveal(selects, selects_all)]
pub fn selects_base<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T,
) {
}

/// The index map `f` of the `Filter` inside a `Map`, run from the start of `fields`, is a selection
/// of the entries of class `e` (`selects`), when the filter accepts the entries whose local is of
/// class `e`. The witnesses of `Filter::produces` are named, so the conclusion is quantifier-free
/// in them. `filter_count`'s first step.
#[thrust_macros::context]
#[thrust_macros::requires(*(*it).0.0.0 == *fields && (*it).0.0.1 == 0)]
#[thrust_macros::requires(forall(|s: Seq<&<L as thrust_models::Model>::Ty>, k: Int, r: bool|
    !(0 <= k && k < s.len() && Filter::<SliceIter<'a, L>, P>::answers((*it).0.1, s, k, r))
        || r == ((*a)[L::index_logic(*s[k])] == *e)))]
#[thrust_macros::ensures(forall(|w: Seq<&<L as thrust_models::Model>::Ty>, o: <Filter<SliceIter<'a, L>, P> as thrust_models::Model>::Ty, s: Seq<&<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, m: Int|
    !(Filter::<SliceIter<'a, L>, P>::produces_at((*it).0, w, o, s, f) && m == w.len())
        || selects::<J, L, K, T>(*fields, *a, *e, f, m, (*fields).len())))]
#[thrust_macros::lemma]
#[thrust::reveal(selects)]
pub fn filter_selects<'a, J, L, K, T, P, M, B>(
    it: &Map<Filter<SliceIter<'a, L>, P>, M>,
    fields: &'a IndexVec<J, L>,
    a: &IndexVec<K, T>,
    e: &T,
) where
    J: Idx + thrust_models::Model,
    L: Idx + thrust_models::Model,
    K: Idx + thrust_models::Model,
    T: thrust_models::Model,
    P: Fn(&&'a L) -> bool,
    M: FnMut(&'a L) -> B,
    B: thrust_models::Model,
{
}

/// `vs` holds, in order, the entries of `l` at the locals of a selection of the entries of class `e`
/// of `fields` (`selects`). Opaque: `selection_of_intro` builds it from a selection, the code that
/// reads it reveals it.
#[thrust_macros::predicate]
#[thrust::opaque]
pub fn selection_of<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model, B: thrust_models::Model>(
    vs: &crate::rustc_index::IndexSlice<J, B>,
    fields: IndexVec<J, L>,
    a: IndexVec<K, T>,
    e: T,
    l: &crate::rustc_index::IndexSlice<L, B>,
) -> bool {
    exists(|f: Array<Int, Int>, m: Int|
        m == (*vs).len()
            && selects::<J, L, K, T>(fields, a, e, f, m, fields.len())
            && forall(|k: Int| !(0 <= k && k < (*vs).len()) || (*vs)[k] == (*l)[L::index_logic(fields[f[k]])]))
}

/// `selection_of` from a selection `f` that holds the entries of `vs`, for every `vs` and `f`.
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|vs: Seq<<B as thrust_models::Model>::Ty>, f: Array<Int, Int>, m: Int|
    !(m == vs.len()
        && selects::<J, L, K, T>(*fields, *a, *e, f, m, (*fields).len())
        && forall(|k: Int| !(0 <= k && k < vs.len()) || vs[k] == (*l)[L::index_logic((*fields)[f[k]])]))
        || selection_of::<J, L, K, T, B>(&vs, *fields, *a, *e, l)))]
#[thrust::reveal(selection_of)]
pub fn selection_of_intro<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model, B: thrust_models::Model>(
    fields: &IndexVec<J, L>,
    a: &IndexVec<K, T>,
    e: &T,
    l: &crate::rustc_index::IndexSlice<L, B>,
) {
}

/// The items a `Map` over a `Filter` of `fields` yields are a `selection_of` the entries of class
/// `e`, when the filter accepts the entries whose local is of class `e` and the closure returns the
/// entry of `l` at the local it is given: `layout()`'s variant's fields are the layouts of the
/// locals Assigned to it, in the order of its entries.
#[thrust_macros::context]
#[thrust_macros::requires(*(*it).0.0.0 == *fields && (*it).0.0.1 == 0)]
#[thrust_macros::requires(forall(|s: Seq<&<L as thrust_models::Model>::Ty>, k: Int, r: bool|
    !(0 <= k && k < s.len() && Filter::<SliceIter<'a, L>, P>::answers((*it).0.1, s, k, r))
        || r == ((*a)[L::index_logic(*s[k])] == *e)))]
#[thrust_macros::requires(forall(|f1: Closure<M>, f2: Closure<M>, x: &<L as thrust_models::Model>::Ty, b: <B as thrust_models::Model>::Ty|
    !(thrust_macros::hist_inv!((*it).1, f1) && thrust_macros::post!(Mut::new(f1, f2)(x), b))
        || b == (*l)[L::index_logic(*x)]))]
#[thrust_macros::ensures(forall(|v: Seq<<B as thrust_models::Model>::Ty>, o: <Map<Filter<SliceIter<'a, L>, P>, M> as thrust_models::Model>::Ty|
    !<Map<Filter<SliceIter<'a, L>, P>, M> as IteratorSpec>::produces(*it, v, o)
        || selection_of::<J, L, K, T, B>(&v, *fields, *a, *e, l)))]
#[thrust_macros::lemma]
pub fn map_selected_entries<'a, J, L, K, T, P, M, B>(
    it: &Map<Filter<SliceIter<'a, L>, P>, M>,
    fields: &'a IndexVec<J, L>,
    a: &IndexVec<K, T>,
    e: &T,
    l: &crate::rustc_index::IndexSlice<L, B>,
) where
    J: Idx + thrust_models::Model,
    L: Idx + thrust_models::Model,
    K: Idx + thrust_models::Model,
    T: thrust_models::Model,
    P: Fn(&&'a L) -> bool,
    M: FnMut(&'a L) -> B,
    B: thrust_models::Model,
{
    filter_selects(it, fields, a, e);
    selection_of_intro(fields, a, e, l);
}

/// A selection of the entries of class `e` below `k` has no more positions than the locals of
/// class `e`, when those entries name distinct locals below `n`: `map_bound` and `acc_bound`
/// joined, `filter_count`'s second step.
#[thrust_macros::lemma]
#[thrust_macros::requires(acc_distinct::<J, L, K, T>(*fields, *a, *e, k))]
#[thrust_macros::requires(forall(|p: Int| !(0 <= p && p < k) || L::index_logic((*fields)[p]) < n))]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !selects::<J, L, K, T>(*fields, *a, *e, f, m, k) || m <= class_cnt::<K, T>(*a, n, *e)))]
pub fn selects_count<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize, n: usize,
) {
    map_bound(fields, a, e, k);
    acc_bound(fields, a, e, k, n);
}

/// A selection below `k` that holds every entry of class `e` below `k`: the index map of a filter
/// that ran to the end of `fields`. Opaque as `selects`.
#[thrust_macros::predicate]
#[thrust::opaque]
pub fn selects_all<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: IndexVec<J, L>,
    a: IndexVec<K, T>,
    e: T,
    f: Array<Int, Int>,
    m: Int,
    k: USize,
) -> bool {
    selects::<J, L, K, T>(fields, a, e, f, m, k)
        && forall(|p: Int| !(0 <= p && p < k && a[L::index_logic(fields[p])] == e)
            || exists(|j: Int| 0 <= j && j < m && f[j] == p))
}

/// A whole selection below `k + 1` is one below `k` with the entry at `k` added when it is of
/// class `e`: the last position is `k` (the map increases and stays below `k + 1`).
#[thrust_macros::lemma]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !(selects_all::<J, L, K, T>(*fields, *a, *e, f, m, k + 1) && (*a)[L::index_logic((*fields)[k])] == *e)
        || (0 < m && f[m - 1] == k && selects_all::<J, L, K, T>(*fields, *a, *e, f, m - 1, k))))]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !(selects_all::<J, L, K, T>(*fields, *a, *e, f, m, k + 1) && !((*a)[L::index_logic((*fields)[k])] == *e))
        || selects_all::<J, L, K, T>(*fields, *a, *e, f, m, k)))]
#[thrust::reveal(selects, selects_all)]
pub fn selects_all_step<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize,
) {
}

/// A whole selection below `k` has exactly as many positions as there are entries of class `e`
/// below `k`: `map_bound` with equality.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !selects_all::<J, L, K, T>(*fields, *a, *e, f, m, k) || m == acc_cnt::<J, L, K, T>(*fields, *a, *e, k)))]
pub fn map_exact<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, k: usize,
) {
    if k > 0 {
        map_exact(fields, a, e, k - 1);
        selects_all_step(fields, a, e, k - 1);
    } else {
        selects_base(fields, a, e);
    }
}

/// An entry of class `e` among the inner items the `Filter` inside a `Map` passed over, from the
/// start of `fields`, is at a position of its index map `f`: the filter rejected the others, which
/// it does only for entries not of class `e`.
#[thrust_macros::context]
#[thrust_macros::requires(*(*it).0.0.0 == *fields && (*it).0.0.1 == 0)]
#[thrust_macros::requires(forall(|s: Seq<&<L as thrust_models::Model>::Ty>, k: Int, r: bool|
    !(0 <= k && k < s.len() && Filter::<SliceIter<'a, L>, P>::answers((*it).0.1, s, k, r))
        || r == ((*a)[L::index_logic(*s[k])] == *e)))]
#[thrust_macros::ensures(forall(|w: Seq<&<L as thrust_models::Model>::Ty>, o: <Filter<SliceIter<'a, L>, P> as thrust_models::Model>::Ty, s: Seq<&<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, p: Int|
    !(Filter::<SliceIter<'a, L>, P>::produces_at((*it).0, w, o, s, f)
        && 0 <= p && p < s.len() && (*a)[L::index_logic((*fields)[p])] == *e)
        || exists(|j: Int| 0 <= j && j < w.len() && f[j] == p)))]
#[thrust_macros::lemma]
pub fn filter_covers_passed<'a, J, L, K, T, P, M, B>(
    it: &Map<Filter<SliceIter<'a, L>, P>, M>,
    fields: &'a IndexVec<J, L>,
    a: &IndexVec<K, T>,
    e: &T,
) where
    J: Idx + thrust_models::Model,
    L: Idx + thrust_models::Model,
    K: Idx + thrust_models::Model,
    T: thrust_models::Model,
    P: Fn(&&'a L) -> bool,
    M: FnMut(&'a L) -> B,
    B: thrust_models::Model,
{
}

/// The entries of `fields` after the inner items the `Filter` inside a `Map` passed over are not
/// of class `e` when the filter then completed: it rejected each of them.
#[thrust_macros::context]
#[thrust_macros::requires(*(*it).0.0.0 == *fields && (*it).0.0.1 == 0)]
#[thrust_macros::requires(forall(|s: Seq<&<L as thrust_models::Model>::Ty>, k: Int, r: bool|
    !(0 <= k && k < s.len() && Filter::<SliceIter<'a, L>, P>::answers((*it).0.1, s, k, r))
        || r == ((*a)[L::index_logic(*s[k])] == *e)))]
#[thrust_macros::ensures(forall(|w: Seq<&<L as thrust_models::Model>::Ty>, o: <Filter<SliceIter<'a, L>, P> as thrust_models::Model>::Ty, fin: <Filter<SliceIter<'a, L>, P> as thrust_models::Model>::Ty, s: Seq<&<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, p: Int|
    !(Filter::<SliceIter<'a, L>, P>::produces_at((*it).0, w, o, s, f)
        && <Filter<SliceIter<'a, L>, P> as IteratorSpec>::completed(Mut::new(o, fin))
        && s.len() <= p && p < (*fields).len())
        || !((*a)[L::index_logic((*fields)[p])] == *e)))]
#[thrust_macros::lemma]
pub fn filter_rejects_rest<'a, J, L, K, T, P, M, B>(
    it: &Map<Filter<SliceIter<'a, L>, P>, M>,
    fields: &'a IndexVec<J, L>,
    a: &IndexVec<K, T>,
    e: &T,
) where
    J: Idx + thrust_models::Model,
    L: Idx + thrust_models::Model,
    K: Idx + thrust_models::Model,
    T: thrust_models::Model,
    P: Fn(&&'a L) -> bool,
    M: FnMut(&'a L) -> B,
    B: thrust_models::Model,
{
}

/// The index map `f` of the `Filter` inside a `Map`, run from the start of `fields` until it
/// completes, is a whole selection of the entries of class `e`: `filter_selects`,
/// `filter_covers_passed` and `filter_rejects_rest` joined.
#[thrust_macros::context]
#[thrust_macros::requires(*(*it).0.0.0 == *fields && (*it).0.0.1 == 0)]
#[thrust_macros::requires(forall(|s: Seq<&<L as thrust_models::Model>::Ty>, k: Int, r: bool|
    !(0 <= k && k < s.len() && Filter::<SliceIter<'a, L>, P>::answers((*it).0.1, s, k, r))
        || r == ((*a)[L::index_logic(*s[k])] == *e)))]
#[thrust_macros::ensures(forall(|w: Seq<&<L as thrust_models::Model>::Ty>, o: <Filter<SliceIter<'a, L>, P> as thrust_models::Model>::Ty, fin: <Filter<SliceIter<'a, L>, P> as thrust_models::Model>::Ty, s: Seq<&<L as thrust_models::Model>::Ty>, f: Array<Int, Int>, m: Int|
    !(Filter::<SliceIter<'a, L>, P>::produces_at((*it).0, w, o, s, f)
        && <Filter<SliceIter<'a, L>, P> as IteratorSpec>::completed(Mut::new(o, fin)) && m == w.len())
        || selects_all::<J, L, K, T>(*fields, *a, *e, f, m, (*fields).len())))]
#[thrust_macros::lemma]
#[thrust::reveal(selects_all)]
pub fn filter_selects_all<'a, J, L, K, T, P, M, B>(
    it: &Map<Filter<SliceIter<'a, L>, P>, M>,
    fields: &'a IndexVec<J, L>,
    a: &IndexVec<K, T>,
    e: &T,
) where
    J: Idx + thrust_models::Model,
    L: Idx + thrust_models::Model,
    K: Idx + thrust_models::Model,
    T: thrust_models::Model,
    P: Fn(&&'a L) -> bool,
    M: FnMut(&'a L) -> B,
    B: thrust_models::Model,
{
    filter_selects(it, fields, a, e);
    filter_covers_passed(it, fields, a, e);
    filter_rejects_rest(it, fields, a, e);
}

/// A completed `Map` over a `Filter` of `fields` yields exactly the entries of class `e`, when the
/// filter accepts the entries whose local is of class `e`: the converse of `filter_count`, which
/// `layout()`'s count of a variant's fields needs. `k` is the length, which a lemma's proof cannot
/// call `len` for.
#[thrust_macros::context]
#[thrust_macros::requires(*(*it).0.0.0 == *fields && (*it).0.0.1 == 0 && k == (*fields).len())]
#[thrust_macros::requires(forall(|s: Seq<&<L as thrust_models::Model>::Ty>, k: Int, r: bool|
    !(0 <= k && k < s.len() && Filter::<SliceIter<'a, L>, P>::answers((*it).0.1, s, k, r))
        || r == ((*a)[L::index_logic(*s[k])] == *e)))]
#[thrust_macros::ensures(forall(|v: Seq<<B as thrust_models::Model>::Ty>, mid: <Map<Filter<SliceIter<'a, L>, P>, M> as thrust_models::Model>::Ty, fin: <Map<Filter<SliceIter<'a, L>, P>, M> as thrust_models::Model>::Ty|
    !(<Map<Filter<SliceIter<'a, L>, P>, M> as IteratorSpec>::produces(*it, v, mid)
        && <Map<Filter<SliceIter<'a, L>, P>, M> as IteratorSpec>::completed(Mut::new(mid, fin)))
        || v.len() == acc_cnt::<J, L, K, T>(*fields, *a, *e, (*fields).len())))]
#[thrust_macros::lemma]
pub fn map_count_exact<'a, J, L, K, T, P, M, B>(
    it: &Map<Filter<SliceIter<'a, L>, P>, M>,
    fields: &'a IndexVec<J, L>,
    a: &IndexVec<K, T>,
    e: &T,
    k: usize,
) where
    J: Idx + thrust_models::Model,
    L: Idx + thrust_models::Model,
    K: Idx + thrust_models::Model,
    T: thrust_models::Model,
    P: Fn(&&'a L) -> bool,
    M: FnMut(&'a L) -> B,
    B: thrust_models::Model,
{
    filter_selects_all(it, fields, a, e);
    map_exact(fields, a, e, k);
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
    filter_selects(it, fields, a, e);
    selects_count(fields, a, e, k, n);
}

/// The items a `Filter` over a slice iterator yields are entries of the slice at or after the
/// iterator's position, so a bound on the indices of those entries holds of them: `Map::new`'s
/// `next_precondition` and `preservation_inv` for a map closure that requires the bound.
#[thrust_macros::context]
#[thrust_macros::requires(forall(|p: USize, i: USize|
    !((*it).0.1 <= p && p < (*(*it).0.0).len() && L::index_is((*(*it).0.0)[p], i)) || i < n))]
#[thrust_macros::ensures(forall(|v: Seq<&<L as thrust_models::Model>::Ty>, o: <Filter<SliceIter<'a, L>, P> as thrust_models::Model>::Ty, j: Int|
    !(<Filter<SliceIter<'a, L>, P> as IteratorSpec>::produces(*it, v, o) && 0 <= j && j < v.len())
        || L::index_logic(*v[j]) < n))]
// The last of two items after others, in the form `preservation_inv` reads.
#[thrust_macros::ensures(forall(|s: Seq<&<L as thrust_models::Model>::Ty>, e1: &<L as thrust_models::Model>::Ty, e2: &<L as thrust_models::Model>::Ty, o: <Filter<SliceIter<'a, L>, P> as thrust_models::Model>::Ty|
    !<Filter<SliceIter<'a, L>, P> as IteratorSpec>::produces(*it, s.push(e1).push(e2), o) || L::index_logic(*e2) < n))]
#[thrust_macros::lemma]
pub fn filter_yields_below<'a, L, P>(it: &Filter<SliceIter<'a, L>, P>, n: usize)
where
    L: Idx + thrust_models::Model,
    P: Fn(&&'a L) -> bool,
{
}

// The weight of a variant's fields (stage 7, sites 4 and 5): the sum of the weights `ts` of the
// locals an injective selection names is at most the sum over the locals of the class, the
// weighted form of `acc_bound` and `map_bound` above. `layout()` does not use them yet.

/// The sum of `ts` over the locals below `k` whose class in `a` is `e`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn class_wsum<K: Idx + thrust_models::Model, T: thrust_models::Model>(a: IndexVec<K, T>, e: T, ts: Seq<Int>, k: USize) -> Int {
    if k <= 0 {
        0
    } else {
        if a[k - 1] == e {
            class_wsum::<K, T>(a, e, ts, k - 1) + ts[k - 1]
        } else {
            class_wsum::<K, T>(a, e, ts, k - 1)
        }
    }
}

/// The sum of `ts` over the locals of the entries among the first `k` of `fields` of class `e`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn acc_wsum<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: IndexVec<J, L>, a: IndexVec<K, T>, e: T, ts: Seq<Int>, k: USize,
) -> Int {
    if k <= 0 {
        0
    } else {
        if a[L::index_logic(fields[k - 1])] == e {
            acc_wsum::<J, L, K, T>(fields, a, e, ts, k - 1) + ts[L::index_logic(fields[k - 1])]
        } else {
            acc_wsum::<J, L, K, T>(fields, a, e, ts, k - 1)
        }
    }
}

/// As `acc_wsum`, over the entries whose local is below `b`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn acc_wlt<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: IndexVec<J, L>, a: IndexVec<K, T>, e: T, ts: Seq<Int>, k: USize, b: USize,
) -> Int {
    if k <= 0 {
        0
    } else {
        if a[L::index_logic(fields[k - 1])] == e && L::index_logic(fields[k - 1]) < b {
            acc_wlt::<J, L, K, T>(fields, a, e, ts, k - 1, b) + ts[L::index_logic(fields[k - 1])]
        } else {
            acc_wlt::<J, L, K, T>(fields, a, e, ts, k - 1, b)
        }
    }
}

/// As `acc_wsum`, over the entries whose local is `x`.
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
pub fn acc_wocc<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    x: USize, fields: IndexVec<J, L>, a: IndexVec<K, T>, e: T, ts: Seq<Int>, k: USize,
) -> Int {
    if k <= 0 {
        0
    } else {
        if a[L::index_logic(fields[k - 1])] == e && L::index_logic(fields[k - 1]) == x {
            acc_wocc::<J, L, K, T>(x, fields, a, e, ts, k - 1) + ts[x]
        } else {
            acc_wocc::<J, L, K, T>(x, fields, a, e, ts, k - 1)
        }
    }
}

/// The weighted L3: one more local below the bound adds its entries' weights.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(acc_wlt::<J, L, K, T>(*fields, *a, *e, *ts, k, b + 1)
    == acc_wlt::<J, L, K, T>(*fields, *a, *e, *ts, k, b) + acc_wocc::<J, L, K, T>(b, *fields, *a, *e, *ts, k))]
pub fn acc_wl3<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, ts: &Seq<Int>, k: usize, b: usize,
) {
    if k > 0 {
        acc_wl3(fields, a, e, ts, k - 1, b);
    }
}

/// The weight of a local's entries is none when it has no entry and its own weight when it has
/// one.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(0 <= (*ts)[x])]
#[thrust_macros::ensures(
    (acc_occ::<J, L, K, T>(x, *fields, *a, *e, k) != 0 || acc_wocc::<J, L, K, T>(x, *fields, *a, *e, *ts, k) == 0)
        && (acc_occ::<J, L, K, T>(x, *fields, *a, *e, k) > 1 || acc_wocc::<J, L, K, T>(x, *fields, *a, *e, *ts, k) <= (*ts)[x]))]
pub fn acc_wocc_le<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    x: usize, fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, ts: &Seq<Int>, k: usize,
) {
    if k > 0 {
        acc_wocc_le(x, fields, a, e, ts, k - 1);
    }
}

/// No weight is below 0.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(b == 0)]
#[thrust_macros::ensures(acc_wlt::<J, L, K, T>(*fields, *a, *e, *ts, k, b) == 0)]
pub fn acc_wl0<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, ts: &Seq<Int>, k: usize, b: usize,
) {
    if k > 0 {
        acc_wl0(fields, a, e, ts, k - 1, b);
    }
}

/// The weighted L5: when each local below `b` occurs at most once among the entries of class
/// `e`, their weight is at most that of the locals of class `e` below `b`.
#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::requires(forall(|x: USize| !(x < b) || acc_occ::<J, L, K, T>(x, *fields, *a, *e, k) <= 1))]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < b) || 0 <= (*ts)[x]))]
#[thrust_macros::ensures(acc_wlt::<J, L, K, T>(*fields, *a, *e, *ts, k, b) <= class_wsum::<K, T>(*a, *e, *ts, b))]
pub fn acc_wl5<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, ts: &Seq<Int>, k: usize, b: usize,
) {
    if b > 0 {
        acc_wl5(fields, a, e, ts, k, b - 1);
        acc_wl3(fields, a, e, ts, k, b - 1);
        acc_zero(fields, a, e, k);
        acc_wocc_le(b - 1, fields, a, e, ts, k);
    } else {
        acc_wl0(fields, a, e, ts, k, b);
    }
}

/// When every entry's local is below `n`, the weight below `n` is the whole weight.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|p: Int| !(0 <= p && p < k) || L::index_logic((*fields)[p]) < n))]
#[thrust_macros::ensures(acc_wlt::<J, L, K, T>(*fields, *a, *e, *ts, k, n) == acc_wsum::<J, L, K, T>(*fields, *a, *e, *ts, k))]
pub fn acc_wall<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, ts: &Seq<Int>, k: usize, n: usize,
) {
    if k > 0 {
        acc_wall(fields, a, e, ts, k - 1, n);
    }
}

/// The weight of the entries of class `e` is at most that of the locals of class `e`.
#[thrust_macros::lemma]
#[thrust_macros::requires(acc_distinct::<J, L, K, T>(*fields, *a, *e, k))]
#[thrust_macros::requires(forall(|p: Int| !(0 <= p && p < k) || L::index_logic((*fields)[p]) < n))]
#[thrust_macros::requires(forall(|x: Int| !(0 <= x && x < n) || 0 <= (*ts)[x]))]
#[thrust_macros::ensures(acc_wsum::<J, L, K, T>(*fields, *a, *e, *ts, k) <= class_wsum::<K, T>(*a, *e, *ts, n))]
pub fn acc_wbound<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, ts: &Seq<Int>, k: usize, n: usize,
) {
    acc_l4_all(fields, a, e, k);
    acc_wl5(fields, a, e, ts, k, n);
    acc_wall(fields, a, e, ts, k, n);
}

/// The sum of `ts` over the locals of the entries of `fields` at the first `m` positions of `f`.
#[thrust_macros::logic]
#[thrust_macros::variant(m)]
pub fn map_wsum<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model>(
    fields: IndexVec<J, L>, ts: Seq<Int>, f: Array<Int, Int>, m: Int,
) -> Int {
    if m <= 0 {
        0
    } else {
        map_wsum::<J, L>(fields, ts, f, m - 1) + ts[L::index_logic(fields[f[m - 1]])]
    }
}

/// The weighted `map_bound`: a selection below `k` selects no more weight than the entries of
/// class `e` below `k`.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|x: Int| 0 <= (*ts)[x]))]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !selects::<J, L, K, T>(*fields, *a, *e, f, m, k)
        || map_wsum::<J, L>(*fields, *ts, f, m) <= acc_wsum::<J, L, K, T>(*fields, *a, *e, *ts, k)))]
pub fn map_wbound<J: Idx + thrust_models::Model, L: Idx + thrust_models::Model, K: Idx + thrust_models::Model, T: thrust_models::Model>(
    fields: &IndexVec<J, L>, a: &IndexVec<K, T>, e: &T, ts: &Seq<Int>, k: usize,
) {
    if k > 0 {
        map_wbound(fields, a, e, ts, k - 1);
        selects_step(fields, a, e, k - 1);
    }
}
