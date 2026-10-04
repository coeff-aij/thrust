//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all

// Soundness check for the integer range: `x + 1` overflows at `x == 255` (it wraps to 0 at run
// time, so the `assert!` fails). The result has type `u8`, whose values are assumed below 256.
// If the result were assumed in range without an obligation, the path on which it is 256 would
// be dropped and the `assert!` would verify; the expected error is the overflow obligation.
#[thrust::callable]
fn f(x: u8) {
    let y = x + 1;
    assert!(y > x);
}

fn main() {}
