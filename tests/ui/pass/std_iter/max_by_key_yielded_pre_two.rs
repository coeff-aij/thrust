//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The key's precondition holds of exactly the two items the iterator yields.
fn main() {
    let key = thrust_macros::closure!(
        requires(*x == 3 || *x == 4),
        ensures(result == *x),
        |x: &u32| -> u64 { *x as u64 },
    );
    let m = Some(3u32).into_iter().chain(Some(4u32)).max_by_key(key);
    assert!(m == Some(4));
}
