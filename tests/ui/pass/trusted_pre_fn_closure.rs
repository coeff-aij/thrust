//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `t1` states `pre!(g(x))`, which `main` discharges, and runs a closure written in its own body
// that calls `g(x)`: `t1`'s code, so the `pre!` covers it.
use thrust_models::Model;

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(true)]
fn t1<T: Model>(_t: T, x: i32) {
    let c = || g(x);
    c()
}

fn main() {
    t1(0i32, 1)
}
