//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A user's generic function that happens to be named like an extracted block, called.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 1)]
fn __block_contract_0<T>(_t: T) -> i64 { 0 }
fn main() { assert!(__block_contract_0(0u8) == 1); }
