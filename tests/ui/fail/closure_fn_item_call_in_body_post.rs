//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The body is checked against the function's postcondition: it returns more than `g(x)`.

#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(thrust_macros::post!(g(x), result))]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x) + 1
}

#[thrust_macros::requires(x < 100)]
#[thrust_macros::ensures(result == x + 1)]
fn inc(x: i32) -> i32 {
    x + 1
}

fn main() {
    apply(&inc, 4);
}
