//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The key's precondition holds of the one item the iterator yields, not of every `u32`.
fn main() {
    let a: Option<u32> = Some(3);
    let key = thrust_macros::closure!(
        requires(*x == 3),
        ensures(result == *x),
        |x: &u32| -> u64 { *x as u64 },
    );
    let m = a.into_iter().max_by_key(key);
    assert!(m == Some(3));
}
