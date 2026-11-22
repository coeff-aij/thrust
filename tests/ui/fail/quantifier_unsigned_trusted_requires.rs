//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The body of a trusted function relies on its `requires` read over Rust values: a caller proves
// the `exists` with a witness of the variable's unsigned type, not with any integer.
use thrust_models::exists;

#[thrust::trusted]
#[thrust_macros::requires(exists(|n: u64| n + x == 10))]
fn at_most_ten(x: u64) {
    if x > 10 {
        panic!()
    }
}

fn main() {
    at_most_ten(20);
}
