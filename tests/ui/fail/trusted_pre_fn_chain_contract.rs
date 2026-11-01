//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `t1` states `pre!(g(x))`, which `main` discharges, but `g(0)` runs in `t3`, a trusted function
// with its own contract, which states nothing of `g`. So `g` must accept every argument there.
use thrust_models::Model;

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t3<T: Model>(_t: T) {
    g(0)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(true)]
fn t1<T: Model>(t: T, x: i32) {
    g(x);
    t3(t)
}

fn main() {
    t1(0i32, 1)
}
