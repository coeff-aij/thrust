//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller

// `g` is checked at each closure it is called with. Only the trusted `t` calls it, not the selected
// `caller`, so this run reaches no instance of it and trusts it for its contract, unless `caller` calls it too, as here, with the closure `t` passes.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    let r = f(1);
    assert!(r != 0);
    r
}

#[thrust::trusted]
#[thrust::callable]
fn t() {
    g(|x| x - 1);
}

#[thrust::callable]
fn caller() {
    let x = 1;
    assert!(x == 1);
    g(|x| x - 1);
}

fn main() {}
