//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The block's `ensures` is all the caller knows: it does not say `result == 6`.
fn main() {
    let n = 5i64;
    let f = thrust_macros::closure!(
        requires(true),
        ensures(result == x + 1),
        |x: i64| -> i64 { x + 1 },
    );
    let y = thrust_macros::block_contract!(
        |n: i64, f| -> i64
        requires(n == 5),
        ensures(result >= n),
        { n + 1 }
    );
    assert!(y == 6);
    let _ = f;
}
