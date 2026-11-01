//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// The function's postcondition is all the call gives.

#[thrust::trusted]
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
    assert!(apply(inc, 4) == 6);
}
