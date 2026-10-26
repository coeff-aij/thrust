//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `skip(5)` over a range of two items hands out nothing.
// Fail twin: both are skipped.

fn main() {
    assert!((0..2).skip(5).count() == 1);
}
