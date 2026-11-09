//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `all` returns `true` only where the predicate accepted every item.
fn main() {
    let v = [1i64, 5, 3];
    let b = v.iter().all(thrust_macros::closure!(
        requires(true),
        ensures(result == (*x > 0)),
        |x: &i64| -> bool { *x > 0 },
    ));
    assert!(b);
}
