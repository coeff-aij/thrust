//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

// A value that fits the target type converts to the same value.
use std::convert::TryInto;

fn main() {
    let a: u64 = 255;
    let x: u8 = a.try_into().unwrap();
    assert!(x == 255);
}
