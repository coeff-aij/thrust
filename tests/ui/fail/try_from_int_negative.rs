//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A negative value does not convert to an unsigned type.
use std::convert::TryFrom;

fn main() {
    let a: i64 = 0;
    assert!(u64::try_from(a).is_err());
}
