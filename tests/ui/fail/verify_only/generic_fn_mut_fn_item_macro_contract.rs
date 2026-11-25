//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=caller

// `generic_fn_mut_fn_item.rs` with the contract of `g` written by `thrust_macros::requires` and
// `ensures`, which expand to an extern spec of `g` that covers all its instances.
//
// `g` is checked at each closure it is called with, a function item among them. Outside the
// selection it is analyzed at the instance the selected `caller` makes with `dec`, which asserts more than holds of the argument 1.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
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
