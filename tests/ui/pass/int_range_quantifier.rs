//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable quantified over a model with a width ranges over its type: `[0, 2^w)` for
// `UIntN<w>`, `[-2^(w-1), 2^(w-1))` for `IntN<w>`.
use thrust_models::model::{IntN, UIntN};
use thrust_models::{exists, forall};

#[thrust_macros::ensures(forall(|i: UIntN<8>| 0 <= i && i < 256))]
#[thrust_macros::ensures(forall(|i: IntN<8>| -128 <= i && i < 128))]
#[thrust_macros::ensures(exists(|i: UIntN<8>| i == 255))]
fn ranges() {}

fn main() {}
