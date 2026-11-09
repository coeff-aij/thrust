//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As iterator_all.rs, with the closure's contract inferred.
fn main() {
    let v = [1i64, 5, 3];
    let b = v.iter().all(|x| *x > 0);
    assert!(b);
}
