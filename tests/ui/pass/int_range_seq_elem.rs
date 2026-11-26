//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::model::Int;
// The model of `Vec<u64>` is a sequence of `UIntN<64>`, whose elements are assumed below `2^64`.
use thrust_models::forall;

#[thrust_macros::ensures(forall(|i: Int|
    (0 <= i && i < (*v).len()) ==> (*v)[i] < 18446744073709551616u128))]
fn words_below(v: &Vec<u64>) {}

fn main() {}
