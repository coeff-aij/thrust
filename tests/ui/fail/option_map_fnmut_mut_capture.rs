//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A closure bound by `let` that borrows `n` mutably is `FnMut`; `Option::map` calls it once and
// drops it, which ends the borrow at the value the call left.
fn main() {
    let mut n: i64 = 0;
    let c = |v: i64| -> i64 { n += v; n };
    let o = Some(5i64).map(c);
    assert!(o == Some(5));
    assert!(n == 6);
}
