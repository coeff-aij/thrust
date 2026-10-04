//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all

// Soundness check for the signed integer range: `-x` overflows at `x == -128` (it wraps to -128 at
// run time, so the `assert!` fails). The expected error is the overflow obligation on the
// negation.
#[thrust::callable]
fn f(x: i8) {
    let y = -x;
    assert!(x == 0 || y != x);
}

fn main() {}
