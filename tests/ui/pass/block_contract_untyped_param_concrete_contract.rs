//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A block-declared type parameter stands for the type the outer variable has, so the block is
// verified at that closure type and its `ensures` may rely on the closure's own contract.
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
        ensures(result == 6),
        { f(n) }
    );
    assert!(y == 6);
}
