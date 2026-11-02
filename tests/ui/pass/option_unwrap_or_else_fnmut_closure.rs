//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `Option::unwrap_or_else` takes its closure at an `FnOnce` bound; a closure bound by `let` is
// `FnMut` and changes its state.
fn main() {
    let mut n: i64 = 0;
    let c = move || -> i64 { n += 1; n };
    let o: Option<i64> = None;
    let r = o.unwrap_or_else(c);
    assert!(r == 1);
}
