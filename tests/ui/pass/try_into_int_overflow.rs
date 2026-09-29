//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// A value past the target type's maximum does not convert.
use std::convert::TryInto;

fn main() {
    let a: u64 = 256;
    let r: Result<u8, _> = a.try_into();
    assert!(r.is_err());
}
