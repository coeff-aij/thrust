//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `pass/int_range_quantifier.rs`: `255` is a `UIntN<8>`.
use thrust_models::forall;
use thrust_models::model::UIntN;

#[thrust_macros::ensures(forall(|i: UIntN<8>| i < 255))]
fn ranges() {}

fn main() {}
