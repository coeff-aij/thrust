//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// No `usize` is below `0`: the binder of an `exists` at an unsigned type ranges over the values
// `>= 0`, so the function does not establish its postcondition.
use thrust_models::exists;

#[thrust_macros::ensures(exists(|i: usize| i < 0))]
fn below_zero() {}

fn main() {}
