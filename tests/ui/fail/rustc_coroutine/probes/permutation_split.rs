//@ignore-on-host: not yet verifiable, PCSat fails on a forall function inside a define-fun-rec: a crash in RecFunGraph.encode by default, a wrong unsat with rec_fun_graph_unknowns off (fptprove thrust-benchmarks unsolved/rec_fun_forall_fun_2026-10-11/)
//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1

use thrust_models::model::{Int, Seq, UInt};
use thrust_models::{forall, Ghost, Model};

type USize = UInt;

// `layout()`'s split of univariant's memory order at `b_start`, over a generic `FieldIdx`: the
// order is a permutation of `0..n` (`arbitrary_of`, stated by `index_is`), the loop is rustc's,
// and the counting lemmas of thrust/lemmas.rs give that the second part has at least
// `n - b_start` entries, each below `n - b_start`, which `invert_bijective_mapping` and the
// variants need. `Idx` is the case study's, with `index_logic` and its law.
#[thrust_macros::context]
trait Idx: Copy + Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::predicate]
    fn can_new(idx: USize) -> bool;

    #[thrust_macros::predicate]
    fn index_is(self, i: USize) -> bool;

    #[thrust_macros::logic]
    fn index_logic(self) -> USize;

    #[thrust_macros::requires(Self::can_new(idx))]
    #[thrust_macros::ensures(Self::index_is(result, idx))]
    fn new(idx: usize) -> Self;

    #[thrust_macros::ensures(Self::index_is(self, result))]
    fn index(self) -> usize;

    #[thrust_macros::law]
    #[thrust_macros::ensures(
        Self::index_logic(*a) >= 0
            && Self::index_is(*a, Self::index_logic(*a))
            && forall(|i: USize| Self::index_is(*a, i) ==> i == Self::index_logic(*a))
    )]
    fn index_logic_is(a: &Self);
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

    #[thrust_macros::logic]
    fn index_logic(self) -> USize {
        self
    }

    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }

    fn index(self) -> usize {
        self as usize
    }

    fn index_logic_is(a: &u32) {}
}

// The counting library of thrust/lemmas.rs, over the model of a vector of indices.

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn occ<I: Idx>(x: USize, s: Vec<I>, k: USize) -> USize
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k <= 0 {
        0
    } else {
        occ::<I>(x, s, k - 1) + if I::index_logic(s[k - 1]) == x { 1 } else { 0 }
    }
}

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn cnt_lt<I: Idx>(s: Vec<I>, k: USize, b: USize) -> USize
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k <= 0 {
        0
    } else {
        cnt_lt::<I>(s, k - 1, b) + if I::index_logic(s[k - 1]) < b { 1 } else { 0 }
    }
}

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn cnt_ge<I: Idx>(s: Vec<I>, k: USize, b: USize) -> USize
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k <= 0 {
        0
    } else {
        cnt_ge::<I>(s, k - 1, b) + if I::index_logic(s[k - 1]) >= b { 1 } else { 0 }
    }
}

#[thrust_macros::predicate]
fn distinct<I: Idx>(s: Vec<I>, k: USize) -> bool
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    forall(|i: Int, j: Int| {
        !(0 <= i && i < j && j < k) || I::index_logic(s[i]) != I::index_logic(s[j])
    })
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(cnt_lt::<I>(s, k, b + 1) == cnt_lt::<I>(s, k, b) + occ::<I>(b, s, k))]
fn l3<I: Idx>(s: Ghost<Vec<I>>, k: usize, b: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k > 0 {
        l3(s, k - 1, b);
    }
}

// The last of the first `k + 1` entries does not occur among the first `j` when they are
// distinct and `j <= k`.
#[thrust_macros::lemma]
#[thrust_macros::variant(j)]
#[thrust_macros::requires(j <= k && distinct::<I>(s, k + 1))]
#[thrust_macros::ensures(occ::<I>(I::index_logic(s[k]), s, j) == 0)]
fn absent<I: Idx>(s: Ghost<Vec<I>>, k: usize, j: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if j > 0 {
        absent(s, k, j - 1);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(distinct::<I>(s, k))]
#[thrust_macros::ensures(forall(|x: UInt| occ::<I>(x, s, k) <= 1))]
fn l4_all<I: Idx>(s: Ghost<Vec<I>>, k: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k > 0 {
        l4_all(s, k - 1);
        absent(s, k - 1, k - 1);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::requires(distinct::<I>(s, k))]
#[thrust_macros::ensures(occ::<I>(x, s, k) <= 1)]
fn l4<I: Idx>(x: usize, s: Ghost<Vec<I>>, k: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    l4_all(s, k);
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(b == 0)]
#[thrust_macros::ensures(cnt_lt::<I>(s, k, b) == 0)]
fn l0<I: Idx>(s: Ghost<Vec<I>>, k: usize, b: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k > 0 {
        l0(s, k - 1, b);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(b)]
#[thrust_macros::requires(forall(|x: UInt| !(x < b) || occ::<I>(x, s, n) <= 1))]
#[thrust_macros::ensures(cnt_lt::<I>(s, n, b) <= b)]
fn l5<I: Idx>(s: Ghost<Vec<I>>, n: usize, b: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if b > 0 {
        l5(s, n, b - 1);
        l3(s, n, b - 1);
    } else {
        l0(s, n, b);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(cnt_lt::<I>(s, k, b) + cnt_ge::<I>(s, k, b) == k)]
fn l6<I: Idx>(s: Ghost<Vec<I>>, k: usize, b: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k > 0 {
        l6(s, k - 1, b);
    }
}

// The permutation split: of `n` distinct indices, at least `n - b` are at least `b`.
#[thrust_macros::lemma]
#[thrust_macros::requires(b <= n && distinct::<I>(s, n))]
#[thrust_macros::ensures(cnt_ge::<I>(s, n, b) >= n - b)]
fn permutation_split<I: Idx>(s: Ghost<Vec<I>>, n: usize, b: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    l4_all(s, n);
    l5(s, n, b);
    l6(s, n, b);
}

// `distinct` from the memory order's injectivity as `arbitrary_of` states it.
#[thrust_macros::lemma]
#[thrust_macros::requires(
    forall(|k: USize, k2: USize, i: USize|
        !(0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2) && I::index_is(s[k], i))
            || !I::index_is(s[k2], i))
)]
#[thrust_macros::ensures(distinct::<I>(s, n))]
fn distinct_of_injective<I: Idx>(s: Ghost<Vec<I>>, n: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
}

// The arm of `layout()` that splits the order, with `Vec` for `IndexVec` and the second part
// returned with its length.
#[thrust_macros::context]
#[thrust_macros::requires(
    in_memory_order.len() == n
        && b_start <= n
        && forall(|k: USize| !(0 <= k && k <= n) || FieldIdx::can_new(k))
        && forall(|k: USize, i: USize|
            !(0 <= k && k < n && FieldIdx::index_is(in_memory_order[k], i)) || i < n)
        && forall(|k: USize, k2: USize, i: USize|
            !(0 <= k && k < n && 0 <= k2 && k2 < n && !(k == k2)
                && FieldIdx::index_is(in_memory_order[k], i))
                || !FieldIdx::index_is(in_memory_order[k2], i))
)]
#[thrust_macros::ensures(
    result.len() >= n - b_start + 1
        && forall(|k: USize, i: USize|
            !(0 <= k && k < result.len() && FieldIdx::index_is(result[k], i)) || i < result.len())
)]
fn split<FieldIdx: Idx>(in_memory_order: Vec<FieldIdx>, n: usize, b_start: usize) -> Vec<FieldIdx>
where
    <FieldIdx as Model>::Ty: Model<Ty = <FieldIdx as Model>::Ty>,
{
    let order = thrust_macros::ghost!(|in_memory_order: Vec<FieldIdx>| -> Vec<FieldIdx> {
        in_memory_order
    });
    thrust_macros::proof!(distinct_of_injective(order, n));
    let mut in_memory_order_a = Vec::<FieldIdx>::new();
    let mut in_memory_order_b = Vec::<FieldIdx>::new();
    for i in in_memory_order {
        thrust_macros::invariant!(
            |iter: std::vec::IntoIter<FieldIdx>,
             iter_old: Ghost<std::vec::IntoIter<FieldIdx>>,
             produced: Ghost<Seq<<FieldIdx as Model>::Ty>>,
             order: Ghost<Vec<FieldIdx>>,
             in_memory_order_a: Vec<FieldIdx>,
             in_memory_order_b: Vec<FieldIdx>,
             n: usize,
             b_start: usize| {
                iter_old.0 == order
                    && iter_old.1 == 0
                    && order.len() == n
                    && b_start <= n
                    && forall(|k: USize| !(0 <= k && k <= n) || FieldIdx::can_new(k))
                    && forall(|k: USize, i: USize|
                        !(0 <= k && k < n && FieldIdx::index_is(order[k], i)) || i < n)
                    && distinct::<FieldIdx>(order, n)
                    && in_memory_order_a.len() + in_memory_order_b.len() == produced.len()
                    && in_memory_order_b.len() == cnt_ge::<FieldIdx>(order, produced.len(), b_start)
                    && forall(|k: USize|
                        !(0 <= k && k < in_memory_order_b.len())
                            || FieldIdx::index_logic(in_memory_order_b[k]) < n - b_start)
            }
        );
        if let Some(j) = i.index().checked_sub(b_start) {
            in_memory_order_b.push(FieldIdx::new(j));
        } else {
            in_memory_order_a.push(i);
        }
    }
    thrust_macros::proof!(permutation_split(order, n, b_start));
    in_memory_order_b
}

fn main() {}
