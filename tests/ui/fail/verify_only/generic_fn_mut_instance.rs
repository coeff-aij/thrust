//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller2

// `g` is verified at each closure it is called with, since its contract does not relate the
// closure's states by `hist_inv!`; the closure in it is analyzed with it. Outside the selection
// it is analyzed at the instance the selected `caller2` makes, whose closure returns 0 at 1, as
// in a run over the whole crate.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    let r = f(1);
    let nonzero = |v: i32| v != 0;
    assert!(nonzero(r));
    r
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
    let mut n = 0;
    g(|x| {
        n += 1;
        x - 1
    });
}

fn main() {}
