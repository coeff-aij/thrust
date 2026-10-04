//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all

// Soundness check for the signed integer range: `x - 1` overflows at `x == -128` (it wraps to 127
// at run time, so the `assert!` fails). The result has type `i8`, whose values are assumed at
// least -128; the expected error is the overflow obligation on the difference.
#[thrust::callable]
fn f(x: i8) {
    let y = x - 1;
    assert!(y < x);
}

fn main() {}
