//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `pass/closure_trusted_pre_shared_type.rs`: `g` rejects the argument `apply2` calls it
// with, and the `pre!` stated of `f`, which holds, does not exempt it.

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply2<F: Fn(i32), G: Fn(i32)>(f: F, g: G, x: i32) {
    f(x);
    g(x)
}

fn main() {
    let mk = |k: i32| move |x: i32| assert!(k == 0 || x > 0);
    apply2(mk(0), mk(1), 0);
}
