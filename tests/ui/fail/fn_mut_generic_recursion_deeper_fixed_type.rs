//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// As `pass/fn_mut_generic_recursion_deeper_fixed_type.rs`: `g` calls itself at the fixed type
// the opaque type `wrapped` returns, deeper than the entry instance's, and the false assertion after the call is found.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F, n: i32) -> i32 {
    if n <= 0 {
        f(1)
    } else {
        g(wrapped(), n - 1)
    }
}

fn wrapped() -> impl FnMut(i32) -> i32 {
    |x| inc(x)
}

fn inc(x: i32) -> i32 {
    x + 1
}

#[thrust::callable]
fn caller() {
    g(inc, 3);
    assert!(false);
}

fn main() {}
