//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected. `#[thrust_macros::predicate(derived)]` is for a trait's predicate.

#[thrust_macros::predicate(derived)] //~ ERROR: `#[thrust_macros::predicate(derived)]` declares
fn q(x: isize) -> bool;

#[thrust_macros::requires(q(x))]
fn f(x: isize) {}

fn main() {}
