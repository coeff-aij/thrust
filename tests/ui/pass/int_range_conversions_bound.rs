//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions

// The range of an integer type is assumed of its values: a `u8` widened to `u32` is below 256,
// and an `i16` is at least -32768.
#[thrust::callable]
fn f(x: u8, y: i16) {
    assert!((x as u32) < 256);
    assert!((y as i32) >= -32768);
}

fn main() {}
