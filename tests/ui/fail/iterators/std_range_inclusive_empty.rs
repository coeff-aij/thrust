//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An inclusive range whose start passes its end has no items.
// Fail twin: it has none.

fn main() {
    assert!((3..=2).count() == 1);
}
