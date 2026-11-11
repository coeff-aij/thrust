//@check-pass
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::{Int, Seq, UInt};
use thrust_models::Model;
use thrust_models::{exists, forall, Ghost};

// The weight of a list of `F`s, each read through `Deref::deref`, whose `post!` at a type
// parameter is a relation: an existential over the sequence of the items' weights, as rustc
// layout's `LayoutCalculator::weight`. `choose!` names the witness of the precondition's
// `weight`, and `witness` proves the postcondition's from the sequence pushed with `x`'s weight.

#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn sum_first(ts: Seq<Int>, k: UInt) -> Int {
    if k <= 0 { 0 } else { sum_first(ts, k - 1) + ts[k - 1] }
}

#[thrust_macros::context]
#[thrust_macros::predicate]
fn weight<F: core::ops::Deref<Target = u64> + Copy + Model>(s: Seq<<F as Model>::Ty>, w: UInt) -> bool {
    exists(|ts: Seq<Int>|
        ts.len() == s.len()
            && forall(|i: Int, d: &u64| !(0 <= i && i < s.len() && thrust_macros::post!(<F as core::ops::Deref>::deref(&s[i]), d)) || ts[i] == *d)
            && w == sum_first(ts, ts.len()))
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::requires(k <= ts.len())]
#[thrust_macros::ensures(sum_first(ts.push(x), k) == sum_first(ts, k))]
fn sum_first_push(ts: Ghost<Seq<Int>>, x: i64, k: usize) {
    if k > 0 {
        sum_first_push(ts, x, k - 1)
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(weight::<F>(*s, w))]
#[thrust_macros::requires(forall(|d: &u64| !thrust_macros::post!(<F as core::ops::Deref>::deref(x), d) || *d == wx))]
#[thrust_macros::ensures(weight::<F>((*s).push(*x), w + wx))]
fn weight_push<F: core::ops::Deref<Target = u64> + Copy + Model>(s: &Vec<F>, x: &F, wx: i64, w: u64) {
    let ts = thrust_macros::choose!(|s: &Vec<F>, w: u64| -> Seq<Int> { weight::<F>(*s, w) });
    thrust_macros::proof!(sum_first_push(ts, wx, s.len()));
    thrust_macros::proof_assert!(|s: &Vec<F>, x: &F, ts: Ghost<Seq<Int>>, wx: i64, w: u64|
        thrust_models::witness(weight::<F>((*s).push(*x), w + wx), ts.push(wx)));
}

fn main() {}
