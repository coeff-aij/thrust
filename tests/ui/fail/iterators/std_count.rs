//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// std's `count` is the number of items produced up to completion.
// Fail twin: the range has five items.

fn main() {
    let n = (0..5).count();
    assert!(n == 4);
}
