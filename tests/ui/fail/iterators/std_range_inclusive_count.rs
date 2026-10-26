//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `0..=3` has four items, its end included.
// Fail twin: the end is one of them.

fn main() {
    assert!((0..=3).count() == 3);
}
