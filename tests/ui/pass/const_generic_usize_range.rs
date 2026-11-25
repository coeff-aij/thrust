//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(x == 5)]
#[thrust_macros::ensures(true)]
fn go<const N: usize>(x: i64) { let m: usize = N; assert!(m >= 0); }
fn main() { go::<0>(5); }
