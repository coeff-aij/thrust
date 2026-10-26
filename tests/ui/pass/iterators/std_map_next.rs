//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// std's `Map` with a concrete closure: each `next` calls the closure on the next item of the
// inner iterator.

fn main() {
    let f = thrust_macros::closure!(
        requires(0 <= x && x < 1000),
        ensures(result == x * 2),
        |x: i64| -> i64 { x * 2 }
    );
    let mut m = (0..10).map(f);
    let a = m.next();
    let b = m.next();
    assert!(matches!(a, Some(0)) && matches!(b, Some(2)));
}
