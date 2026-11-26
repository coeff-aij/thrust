//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A parameter written without a type takes the type of the outer variable, here a closure type
// that cannot be written: the extracted function takes it as a type parameter of its own,
// instantiated at the variable's type. `n` keeps its value, and `f` is not touched.
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
        ensures(result == n + 1),
        { n + 1 }
    );
    assert!(y == 6);
    assert!(f(n) == 6);
}
