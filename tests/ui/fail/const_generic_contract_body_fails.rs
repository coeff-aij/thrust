//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires((*a)[0] == 5)]
#[thrust_macros::ensures(true)]
fn go<const N: usize>(a: &mut [i64; 2]) { assert!(false); }
fn main() { let mut arr = [5i64, 0]; go::<0>(&mut arr); }
