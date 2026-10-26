//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// A `for` over `(0..=n).rev()` with the loop invariant inferred: every item lies in the range, its
// end included.

fn count(n: i64) {
    for i in (0..=n).rev() {
        assert!(0 <= i && i <= n);
    }
}

fn main() {
    count(3);
}
