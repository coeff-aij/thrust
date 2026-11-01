//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The `requires` states the `pre!` of another function, whose type only mentions `F`: that is not
// the closure's, so the closure must accept every argument.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn helper<H: Fn(i32)>(x: i32) {}

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(helper::<F>(x)))]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply(|x: i32| assert!(x > 0), 0);
}
