//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At a type parameter bounded by `Fn`, `hist_inv!` is the equality of states, as no call
// changes an `Fn` closure.
#[thrust_macros::requires(thrust_macros::hist_inv!(f, g))]
#[thrust_macros::ensures(f == g)]
fn same<F: Fn() -> i64>(f: F, g: F) {}

fn main() {}
