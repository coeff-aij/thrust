//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=all

// Soundness check for the integer range: `x * 2` overflows for `x >= 2^31` (it wraps at run
// time, so the `assert!` fails). The expected error is the overflow obligation on the product.
#[thrust::callable]
fn f(x: u32) {
    let y = x * 2;
    assert!(y >= x);
}

fn main() {}
