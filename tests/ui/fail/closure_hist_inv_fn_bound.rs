//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At a type parameter bounded by `FnMut`, `hist_inv!` relates states a call may change.
#[thrust_macros::requires(thrust_macros::hist_inv!(f, g))]
#[thrust_macros::ensures(f == g)]
fn same<F: FnMut() -> i64>(f: F, g: F) {}

fn main() {}
