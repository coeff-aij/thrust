//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `max_by_key` of one item is that item.
fn main() {
    let a: Option<u32> = Some(3);
    let m = a.into_iter().max_by_key(|x| *x as u64);
    assert!(m == Some(3));
}
