//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// std's `filter`: its first item is the first the predicate accepts. PCSat gives no answer on a
// wrong item (no answer in 120 s on `Some(6)`), so the fail twin breaks the predicate instead.

fn main() {
    let c = thrust_macros::closure!(
        ensures(result == (*x >= 5)),
        |x: &i64| -> bool { *x >= 5 },
    );
    let mut it = (0..10).filter(c);
    let a = it.next();
    assert!(matches!(a, Some(5)));
}
