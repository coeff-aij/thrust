//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `any` returns `false` where the predicate rejects every item.
fn main() {
    let v = [1i64, 2, 3];
    let b = v.iter().any(thrust_macros::closure!(
        requires(true),
        ensures(result == (*x > 4)),
        |x: &i64| -> bool { *x > 4 },
    ));
    assert!(!b);
}
