//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A function item handed to std code (Option::map): its obligation is stated at the call.
fn inc(x: i32) -> i32 { assert!(x < 100); x + 1 }
fn main() { let o = Some(100).map(inc); assert!(o == Some(101)); }
