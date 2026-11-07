//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller

// `g` is checked at each closure it is called with, a function item among them. Outside the
// selection it is analyzed at the instance the selected `caller` makes with `dec`, which asserts more than holds of the argument 1.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    f(1)
}

fn dec(x: i32) -> i32 {
    assert!(x > 5);
    x - 1
}

#[thrust::callable]
fn caller() {
    g(dec);
}

fn main() {}
