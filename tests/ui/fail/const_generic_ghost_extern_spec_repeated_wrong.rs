//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn go<const A: usize, const B: usize>() -> usize { B }
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == A)]
fn _extern_spec_go<const A: usize>() -> usize { go::<A, A>() }
fn main() { let r = go::<1, 2>(); assert!(r == 1); }
