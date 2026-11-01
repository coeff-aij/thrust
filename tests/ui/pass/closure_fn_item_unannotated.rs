//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A function item without a contract written, passed for a closure type parameter: its precondition is inferred.
fn inc(x: i32) -> i32 { assert!(x < 100); x + 1 }
fn apply<G: Fn(i32) -> i32>(g: G, x: i32) -> i32 { g(x) }
fn main() { assert!(apply(inc, 4) == 5); }
