//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// The body of a generic function is checked even when the only call to it passes
// type arguments that are still type parameters.

fn bad<T>(_t: T) -> i64 {
    let n = 1i64;
    assert!(n == 2);
    5
}

#[thrust::callable]
fn check<T>(t: T) {
    bad(t);
}

fn main() {}
