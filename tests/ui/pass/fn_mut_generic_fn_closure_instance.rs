//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g` is verified at each closure it is called with, since its contract does not relate the
// closure's states by `hist_inv!` (D34). `caller1`'s `FnMut` closure is such an instance, so `g`
// gets no analysis over `F`; `caller`'s closure, of kind `Fn` with a written contract, is
// analyzed at its own instance, where the closure's precondition holds of 1.

#[thrust::callable]
fn g<F: FnMut(i32) -> i32>(mut f: F) -> i32 {
    f(1)
}

#[thrust::callable]
fn caller() {
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result == x),
        |x: i32| -> i32 { x },
    );
    g(f);
}

#[thrust::callable]
fn caller1() {
    let mut n = 0;
    g(|x| {
        n += 1;
        x + 1
    });
}

fn main() {}
