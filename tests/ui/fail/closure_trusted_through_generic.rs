//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A generic function with a written contract that hands its closure on to a trusted function
// stating no `pre!` of it must state that the closure accepts every argument.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply<F: Fn(i32)>(f: F, x: i32) {
    f(x)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn wrap<F: Fn(i32)>(f: F) {
    apply(f, 0)
}

fn main() {
    let y = 1;
    wrap(move |_: i32| assert!(y == 1));
}
