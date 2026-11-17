//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A generic function whose contract names `post!` of a trait method at its type parameter, called
// at `i32`, gets the contract of the impl the method resolves to there.
use thrust_models::Model;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(thrust_macros::post!(<A as Clone>::clone(&x), result))]
fn f<A: Clone + Model>(x: A) -> A {
    x.clone()
}

fn main() {
    let y = f(3i32);
    assert!(y == 3);
}
