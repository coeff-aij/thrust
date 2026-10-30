//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `pre!` under `!` in the `requires` does not ask for it, so the closure must accept every
// argument.

#[thrust::trusted]
#[thrust_macros::requires(!thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

fn main() {
    apply(|x: i32| assert!(x > 0), 0);
}
