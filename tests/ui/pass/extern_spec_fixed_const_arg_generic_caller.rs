//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The spec fixes `B := 3` of a function that takes its const parameters as ghost arguments, so it
// is the contract of `go` under the premise `B == 3`, and a caller generic over `M` meets it
// when its own contract gives `M == 3`.

fn go<const A: usize, const B: usize>() -> usize { A + B }
#[thrust::extern_spec_fn]
#[thrust_macros::requires(A <= 100)]
#[thrust_macros::ensures(result == A + 3)]
fn _extern_spec_go<const A: usize>() -> usize { go::<A, 3>() }

#[thrust_macros::requires(M == 3)]
#[thrust_macros::ensures(result == 4)]
fn via<const M: usize>() -> usize { go::<1, M>() }

fn main() { let r = via::<3>(); assert!(r == 4); }
