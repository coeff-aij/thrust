//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// A negative value does not convert to an unsigned type.
use std::convert::TryFrom;

fn main() {
    let a: i64 = -1;
    assert!(u64::try_from(a).is_err());
}
