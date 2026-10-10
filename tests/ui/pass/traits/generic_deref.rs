//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use std::ops::Deref;
use thrust_models::forall;

#[thrust_macros::requires(forall(|f: F, r: &u64|
    thrust_macros::post!(<F as Deref>::deref(&f), r) ==> *r > 0))]
#[thrust_macros::ensures(result > 0)]
fn read<F: Deref<Target = u64> + Copy>(x: F) -> u64 {
    *x
}

fn main() {}
