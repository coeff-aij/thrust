//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `pre!` of a function item takes as many arguments as the function.

#[thrust_macros::requires(x < 100)]
#[thrust_macros::ensures(result == x + 1)]
fn inc(x: i32) -> i32 {
    x + 1
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x, x)))] //~ ERROR: `pre!`/`post!` arity mismatch
#[thrust_macros::ensures(true)]
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 {
    g(x)
}

fn main() {
    apply(inc, 200);
}
