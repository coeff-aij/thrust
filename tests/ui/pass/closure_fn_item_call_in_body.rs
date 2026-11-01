//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// An analyzed generic function calls its parameter `g`, which a call instantiates with a function item, or a reference to one: the call runs the function under its contract.

#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

#[thrust_macros::requires(x < 100)]
#[thrust_macros::ensures(result == x + 1)]
fn inc(x: i32) -> i32 {
    x + 1
}

fn main() {
    assert!(apply(inc, 4) == 5);
    assert!(apply(&inc, 4) == 5);
}
