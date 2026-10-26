//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `(0..3).rev()` hands out the range's last item first.
// Fail twin: the range's end, which it excludes.

fn main() {
    let mut r = (0..3).rev();
    assert!(matches!(r.next(), Some(3)));
}
