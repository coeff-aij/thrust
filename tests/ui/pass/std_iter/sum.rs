//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `sum` adds the items the iterator yields.
fn main() {
    let mut v: Vec<usize> = Vec::new();
    v.push(1);
    v.push(2);
    let s: usize = v.into_iter().sum();
    assert!(s == 3);
}
