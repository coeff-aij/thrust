//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `pass/int_range_quantifier.rs`: no `UIntN<8>` is `256`.
use thrust_models::exists;
use thrust_models::model::UIntN;

#[thrust_macros::ensures(exists(|i: UIntN<8>| i == 256))]
fn ranges() {}

fn main() {}
