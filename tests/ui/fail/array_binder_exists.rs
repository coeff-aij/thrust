//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// No array of type `[i64; 2]` has length 3, so the `exists` has no witness.
use thrust_models::exists;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(exists(|a: [i64; 2]| a.len() == 3))]
fn f() {}

fn main() {}
