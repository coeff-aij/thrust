//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A value past the target type's maximum does not convert.
use std::convert::TryInto;

fn main() {
    let a: u64 = 255;
    let r: Result<u8, _> = a.try_into();
    assert!(r.is_err());
}
