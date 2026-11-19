//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g` is verified at each closure it is called with, since its contract does not relate the
// closure's states by `hist_inv!` (D34). `caller1`'s `FnMut` closure is such an instance, so `g`
// gets no analysis over `F`; `caller2` passes the function item `dec`, analyzed at its own
// instance, where `dec`'s assertion does not hold of 1.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    let r = f(1);
    assert!(r != 0);
    r
}

fn dec(x: i32) -> i32 {
    assert!(x > 5);
    x + 1
}

#[thrust::callable]
fn caller1() {
    let mut n = 0;
    g(|x| {
        n += 1;
        x + 1
    });
}

#[thrust::callable]
fn caller2() {
    g(dec);
}

fn main() {}
