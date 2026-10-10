//@ignore-on-host: not yet verifiable, PCSat fails on a forall function inside a define-fun-rec: a crash in RecFunGraph.encode by default, a wrong unsat with rec_fun_graph_unknowns off (fptprove thrust-benchmarks unsolved/rec_fun_forall_fun_2026-10-11/)
//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::forall;
use thrust_models::model::{Int, UInt};
use thrust_models::Model;

// The counting lemmas of lemma_count_*.rs over a slice of a generic index type, as rustc's
// `IndexVec` holds them: the counts read each entry through the trait's logic function
// `index_logic`, a forall function in the generic proofs, and `main` uses `last_high` at `u32`.
// `last_high` splits the entries at `b` as rustc does, by `checked_sub` and `I::new`.

#[thrust_macros::context]
trait Idx: Copy + Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::logic]
    fn index_logic(self) -> usize;

    #[thrust_macros::predicate]
    fn can_new(idx: UInt) -> bool;

    #[thrust_macros::requires(Self::can_new(idx))]
    #[thrust_macros::ensures(Self::index_logic(result) == idx)]
    fn new(idx: usize) -> Self;

    #[thrust_macros::ensures(result == Self::index_logic(self))]
    fn index(self) -> usize;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::index_logic(*x) >= 0)]
    fn index_nonneg(x: &Self);
}

#[thrust_macros::context]
impl Idx for u32 {
    #[thrust_macros::logic]
    fn index_logic(self) -> usize {
        self
    }

    #[thrust_macros::predicate]
    fn can_new(idx: UInt) -> bool {
        idx <= 4294967295usize
    }

    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }

    fn index(self) -> usize {
        self as usize
    }

    fn index_nonneg(x: &u32) {}
}

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn occ<I: Idx>(x: usize, s: &[I], k: usize) -> usize
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
fn cnt_lt<I: Idx>(s: &[I], k: usize, b: usize) -> usize
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k <= 0 {
        0
    } else {
        cnt_lt::<I>(s, k - 1, b) + if I::index_logic(s[k - 1]) < b { 1 } else { 0 }
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(cnt_lt::<I>(s, k, b + 1) == cnt_lt::<I>(s, k, b) + occ::<I>(b, s, k))]
fn l3<I: Idx>(s: &[I], k: usize, b: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k > 0 {
        l3(s, k - 1, b);
    }
}


#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn cnt_ge<I: Idx>(s: &[I], k: usize, b: usize) -> usize
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
fn distinct<I: Idx>(s: &[I], k: usize) -> bool
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    forall(|i: Int, j: Int| {
        !(0 <= i && i < j && j < k) || I::index_logic(s[i]) != I::index_logic(s[j])
    })
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(forall(|i: Int| !(0 <= i && i < k) || I::index_logic(s[i]) != I::index_logic(x)))]
#[thrust_macros::ensures(occ::<I>(I::index_logic(x), s, k) == 0)]
fn absent<I: Idx>(x: I, s: &[I], k: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k > 0 {
        absent(x, s, k - 1);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(k <= s.len() && distinct::<I>(s, k))]
#[thrust_macros::ensures(forall(|x: UInt| occ::<I>(x, s, k) <= 1))]
fn l4_all<I: Idx>(s: &[I], k: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k > 0 {
        l4_all(s, k - 1);
        absent(s[k - 1], s, k - 1);
    }
}

#[thrust_macros::lemma]
#[thrust_macros::requires(k <= s.len() && distinct::<I>(s, k))]
#[thrust_macros::ensures(occ::<I>(x, s, k) <= 1)]
fn l4<I: Idx>(x: usize, s: &[I], k: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    l4_all(s, k);
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(b == 0)]
#[thrust_macros::ensures(cnt_lt::<I>(s, k, b) == 0)]
fn l0<I: Idx>(s: &[I], k: usize, b: usize)
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
fn l5<I: Idx>(s: &[I], n: usize, b: usize)
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
fn l6<I: Idx>(s: &[I], k: usize, b: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    if k > 0 {
        l6(s, k - 1, b);
    }
}

#[thrust_macros::predicate]
fn distinct_below<I: Idx>(s: &[I], n: usize) -> bool
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    n == s.len()
        && distinct::<I>(s, n)
        && forall(|i: Int| !(0 <= i && i < n) || I::index_logic(s[i]) < n)
}

#[thrust_macros::lemma]
#[thrust_macros::requires(b <= n && distinct_below::<I>(s, n))]
#[thrust_macros::ensures(cnt_ge::<I>(s, n, b) >= n - b)]
fn below_count<I: Idx>(s: &[I], n: usize, b: usize)
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    l4_all(s, n);
    l5(s, n, b);
    l6(s, n, b);
}

#[thrust_macros::context]
#[thrust_macros::requires(
    b < n
        && distinct_below::<I>(s, n)
        && forall(|j: UInt| !(j < n) || I::can_new(j))
)]
fn last_high<I: Idx>(s: &[I], n: usize, b: usize) -> I
where
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
{
    let mut low: Vec<I> = Vec::new();
    let mut high: Vec<I> = Vec::new();
    let mut t = 0;
    while t < n {
        thrust_macros::invariant!(|s: &[I], n: usize, b: usize, t: usize, high: Vec<I>| {
            t <= n
                && b < n
                && distinct_below::<I>(s, n)
                && forall(|j: UInt| !(j < n) || I::can_new(j))
                && high.len() == cnt_ge::<I>(s, t, b)
        });
        let i = s[t];
        if let Some(j) = i.index().checked_sub(b) {
            high.push(I::new(j));
        } else {
            low.push(i);
        }
        t += 1;
    }
    thrust_macros::proof!(below_count(s, n, b));
    high[n - b]
}

fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(0);
    let _ = last_high(&v, 2, 1);
}
