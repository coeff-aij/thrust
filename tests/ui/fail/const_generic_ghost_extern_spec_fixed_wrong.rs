//@error-in-other-file: has no specification at these arguments
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The spec fixes `B := 3`, so it covers only those instances; the call at `go::<1, 5>` stops as an
// uncovered instance (on develop it was rejected as `Unsat` by the spec's fixed-argument premise).
fn go<const A: usize, const B: usize>() -> usize { A + B }
#[thrust::extern_spec_fn]
#[thrust_macros::requires(A <= 100)]
#[thrust_macros::ensures(result == A + 3)]
fn _extern_spec_go<const A: usize>() -> usize { go::<A, 3>() }
fn main() { let r = go::<1, 5>(); assert!(r == 4); }
