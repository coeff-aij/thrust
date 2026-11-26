//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn go<const A: usize, const B: usize>() -> usize { A + B }
#[thrust::extern_spec_fn]
#[thrust_macros::requires(A <= 100)]
#[thrust_macros::ensures(result == A + 3)]
fn _extern_spec_go<const A: usize>() -> usize { go::<A, 3>() }
fn main() { let r = go::<1, 3>(); assert!(r == 4); }
