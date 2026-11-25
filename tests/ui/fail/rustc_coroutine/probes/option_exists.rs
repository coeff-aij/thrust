//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;

/// The model of `usize`, which carries its width while `THRUST_INT_RANGE` is set.
#[cfg(not(thrust_int_range))]
type USize = thrust_models::model::UInt;
#[cfg(thrust_int_range)]
type USize = thrust_models::model::UIntN<64>;


#[thrust_macros::requires(exists(|k: USize| x == Some(k) && k < 5))]
#[thrust_macros::ensures(true)]
fn test(x: Option<usize>) {
    let v = x.unwrap();
    assert!(v < 4);
}

fn main() {
    test(Some(4));
}
