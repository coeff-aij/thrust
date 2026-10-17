//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` over `(0..n).rev()` with the loop invariant inferred: `Rev` takes the range's items
// from the back through `next_back`.
// Fail twin: the last item is `0`.

fn count(n: i64) {
    for i in (0..n).rev() {
        assert!(0 < i && i < n);
    }
}

fn main() {
    count(3);
}
