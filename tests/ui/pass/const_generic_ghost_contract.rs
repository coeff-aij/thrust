//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(N == 3)]
#[thrust_macros::ensures(result == N)]
fn go<const N: usize>() -> usize { N }
fn main() { let r = go::<3>(); assert!(r == 3); }
