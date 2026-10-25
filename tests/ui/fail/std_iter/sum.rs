//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The sum is the sum of the items.
fn main() {
    let mut v: Vec<usize> = Vec::new();
    v.push(1);
    v.push(2);
    let s: usize = v.into_iter().sum();
    assert!(s == 4);
}
