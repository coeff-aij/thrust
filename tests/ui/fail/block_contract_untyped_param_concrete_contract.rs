//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The block is verified at the closure type of its declared type parameter, so a wrong `ensures`
// fails against the closure's own contract.
fn main() {
    let n = 5i64;
    let f = thrust_macros::closure!(
        requires(true),
        ensures(result == x + 1),
        |x: i64| -> i64 { x + 1 },
    );
    let y = thrust_macros::block_contract!(
        <F: Fn(i64) -> i64>
        |n: i64, f: F| -> i64
        requires(n == 5),
        ensures(result == 7),
        { f(n) }
    );
    assert!(y == 7);
}
