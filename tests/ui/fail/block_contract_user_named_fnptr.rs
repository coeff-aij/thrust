//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// Called through a function pointer only.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 1)]
fn __block_contract_0<T>(_t: T) -> i64 { 0 }
fn apply(f: fn(u8) -> i64) -> i64 { f(0) }
fn main() { assert!(apply(__block_contract_0::<u8>) == 1); }
