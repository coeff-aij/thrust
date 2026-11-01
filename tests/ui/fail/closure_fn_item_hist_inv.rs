//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `hist_inv!` relates the states of a closure; a function item has none, and is rejected.

#[thrust::trusted]
#[thrust_macros::ensures(thrust_macros::hist_inv!(g, result))] //~ ERROR: `hist_inv!` is not supported
fn keep<G: Fn(i32) -> i32>(g: G) -> G {
    g
}

fn inc(x: i32) -> i32 {
    x + 1
}

fn main() {
    keep(inc);
}
