//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// A generic function called at type arguments that are still type parameters
// contributes its result to the caller.

fn five<T>(_t: T) -> i64 {
    5
}

#[thrust::callable]
fn check<T>(t: T) {
    assert!(five(t) == 6);
}

fn main() {}
