//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `nth` hands out the item after `n` others and leaves the iterator after it.
// Fail twin: the item after the one `nth` handed out.

fn main() {
    let mut r = 0..10;
    assert!(matches!(r.nth(3), Some(3)));
    assert!(matches!(r.next(), Some(5)));
}
