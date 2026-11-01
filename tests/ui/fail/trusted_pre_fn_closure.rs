//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `t1` states `pre!(g(x))`, which `main` discharges, and runs a closure that `t3` returns. The
// closure is written in `t3`, so `g(0)` is `t3`'s code, whose contract states nothing of `g`.
// So `g` must accept every argument there.
use thrust_models::Model;

fn g(x: i32) {
    assert!(x > 0)
}

#[thrust::trusted]
#[thrust::callable]
fn t3<T: Model>(_t: T) -> impl Fn() {
    || g(0)
}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(x)))]
#[thrust_macros::ensures(true)]
fn t1<T: Model>(t: T, x: i32) {
    g(x);
    t3(t)()
}

fn main() {
    t1(0i32, 1)
}
