//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A reference to a function item whose contract is inferred, for a trusted callee that states
// `pre!` of `g`: the call states the function's precondition as it does for the item itself.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

fn inc(x: i32) -> i32 {
    assert!(x < 100);
    x + 1
}

fn main() {
    assert!(apply(&inc, 4) == 5);
}
