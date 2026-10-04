//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `pass/int_range_seq_elem.rs`: an element of a `Vec<u64>` may be `2^64 - 1`.
use thrust_models::forall;

#[thrust_macros::ensures(forall(|i: thrust_models::model::Int|
    (0 <= i && i < (*v).len()) ==> (*v)[i] < 18446744073709551615u128))]
fn words_below(v: &Vec<u64>) {}

fn main() {}
