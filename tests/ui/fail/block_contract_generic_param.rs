//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The block calls `f` at `n == 5`, which the closure's `requires(x > 5)` does not allow.
fn main() {
    let n = 5i64;
    let f = thrust_macros::closure!(
        requires(x > 5),
        ensures(result == x + 1),
        |x: i64| -> i64 { x + 1 },
    );
    let y = thrust_macros::block_contract!(
        <F: Fn(i64) -> i64>
        |n: i64, f: F| -> i64
        requires(n == 5),
        ensures(true),
        { f(n) }
    );
    let _ = y;
}
