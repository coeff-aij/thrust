//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(x == 5)]
#[thrust_macros::ensures(true)]
fn go<const N: u8>(x: i64) { let m = N as i64; assert!(m >= 0 && m <= 254); }
fn main() { go::<0>(5); }
