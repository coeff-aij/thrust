//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted `ensures` quantifying over `char` is assumed with its variable a Unicode scalar
// value, so it states what it says of Rust values, and nothing false: `result` is `char::MAX`.
// Z3 answers `unknown` on the fail twin, so both twins run PCSat.
use thrust_models::forall;

#[thrust::trusted]
#[thrust_macros::ensures(forall(|c: char| c <= result))]
fn max_char() -> char {
    char::MAX
}

fn main() {
    let m = max_char();
    assert!(m == char::MAX);
}
