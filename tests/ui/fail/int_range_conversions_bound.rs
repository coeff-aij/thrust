//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions

// The twin of `pass/int_range_conversions_bound.rs`: a `u8` may be 255.
#[thrust::callable]
fn f(x: u8) {
    assert!((x as u32) < 255);
}

fn main() {}
