//@no-rustfix
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Fork issue #278: the weight of a concatenation, an existential over a Seq<Int>, without a ghost witness.

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

// The weight of two lists put together, from the weight of each: the goal's existential needs
// the concatenation of the premises' two sequences of weights.
#[thrust_macros::context]
#[thrust_macros::lemma]
#[thrust_macros::requires(weight::<F>(*s, ws))]
#[thrust_macros::requires(weight::<F>(*t, wt))]
#[thrust_macros::ensures(weight::<F>((*s).concat(*t), ws + wt + 1))]
fn weight_concat<F: core::ops::Deref<Target = u64> + Copy + Model>(s: &Vec<F>, t: &Vec<F>, ws: u64, wt: u64) {} //~ ERROR: verification error: Unsat

fn main() {}
