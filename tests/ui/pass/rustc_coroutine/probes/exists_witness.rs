//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Fork issue #278: proving an existential over a Seq<Int> (the weight of a pushed list) from a named witness.

use thrust_models::{exists, forall};
use thrust_models::model::{Int, Seq, UInt};
use thrust_models::Model;

// The weight of a list of `F`s, each read through `Deref::deref`, whose `post!` at a type
// parameter is a relation: as rustc_coroutine's `LayoutCalculator::weight` (layout.rs), an
// existential over the sequence of the items' weights.

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

#[thrust_macros::context]
#[thrust_macros::predicate]
fn weights_are<F: core::ops::Deref<Target = u64> + Copy + Model>(s: Seq<<F as Model>::Ty>, ts: Seq<Int>) -> bool {
    ts.len() == s.len()
        && forall(|i: Int, d: &u64| !(0 <= i && i < s.len() && thrust_macros::post!(<F as core::ops::Deref>::deref(&s[i]), d)) || ts[i] == *d)
}

// With the witness named (a ghost argument), `weight` of the pushed list: the goal's existential
// has the term `ts.push(wx)` in scope.
#[thrust_macros::context]
#[thrust_macros::lemma]
#[thrust_macros::requires(weights_are::<F>(*s, *ts))]
#[thrust_macros::requires(forall(|d: &u64| !thrust_macros::post!(<F as core::ops::Deref>::deref(x), d) || *d == wx))]
#[thrust_macros::requires(w == sum_first(*ts, (*ts).len()) + wx)]
#[thrust_macros::ensures(weight::<F>((*s).push(*x), w))]
fn weight_push_named<F: core::ops::Deref<Target = u64> + Copy + Model>(s: &Vec<F>, ts: &Seq<Int>, x: &F, wx: u64, w: u64) {}

fn main() {}
