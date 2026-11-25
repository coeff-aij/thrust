//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A block declares a type parameter with its bound, `<F: Fn(i64) -> i64>`: the extracted function
// is generic over it and is verified for every `F` meeting the bound, and the call instantiates it
// at the closure type of the variable. The block calls `f`, so `requires` states its precondition.
fn main() {
    let n = 5i64;
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result == x + 1),
        |x: i64| -> i64 { x + 1 },
    );
    let y = thrust_macros::block_contract!(
        <F: Fn(i64) -> i64>
        |n: i64, f: F| -> i64
        requires(n == 5 && thrust_macros::pre!(f(n))),
        ensures(true),
        { f(n) }
    );
    assert!(f(n) == 6);
    let _ = y;
}
