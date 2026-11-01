//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// An analyzed generic function calls its parameter `g`, which a call instantiates with a reference to a closure: `&F` calls `F`, under the closure's contract.

#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}


fn main() {
    let k = 3;
    let a = move |x: i32| {
        assert!(x > k);
        x + k
    };
    assert!(apply(&a, 4) == 7);
}
