//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// Of two items with the greatest key, `max_by_key` returns the last, not the first.
fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(2);
    v.push(3);
    let m = v.into_iter().max_by_key(|x| *x / 2);
    assert!(m == Some(2));
}
