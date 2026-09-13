//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// A mutable reference written through a generic function is tracked at a call site
// whose type arguments are still type parameters.

fn set<T>(r: &mut i64, _t: T) {
    *r = 5;
}

#[thrust::callable]
fn check<T>(t: T) {
    let mut n = 0i64;
    set(&mut n, t);
    assert!(n == 5);
}

fn main() {}
