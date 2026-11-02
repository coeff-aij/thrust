//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `Option::map` takes its closure at an `FnOnce` bound; a closure bound by `let` is `FnMut` and
// changes its state.
fn main() {
    let mut n: i64 = 0;
    let c = move |v: i64| -> i64 { n += v; n };
    let o = Some(5i64).map(c);
    assert!(o == Some(5));
}
