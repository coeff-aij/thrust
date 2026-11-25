//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller

// `g` is checked at each closure it is called with. Outside the selection it is analyzed at the
// instance the selected `caller` makes, whose closure's written precondition `x > 5` does not hold of the argument 1.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    f(1)
}

#[thrust::callable]
fn caller() {
    let f = thrust_macros::closure!(
        requires(x > 5),
        ensures(result == x),
        |x: i32| -> i32 { x },
    );
    g(f);
}

fn main() {}
