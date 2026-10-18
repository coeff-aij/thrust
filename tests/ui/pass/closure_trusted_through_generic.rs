//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `fail/closure_trusted_through_generic.rs`: `wrap` without a contract is analyzed at
// the closure, which accepts every argument.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn wrap<F: Fn(i32)>(f: F) {
    apply(f, 0)
}

fn main() {
    let y = 1;
    wrap(move |_: i32| assert!(y == 1));
}
