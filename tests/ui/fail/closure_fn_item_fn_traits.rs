//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A function item for FnMut, FnOnce and multi-argument bounds, and a reference to one.
#[thrust_macros::requires(x < 100)]
#[thrust_macros::ensures(result == x + 1)]
fn inc(x: i32) -> i32 { x + 1 }
fn apply<G: FnMut(i32) -> i32>(mut g: G, x: i32) -> i32 { g(x) }
fn apply1<G: FnOnce(i32) -> i32>(g: G, x: i32) -> i32 { g(x) }
fn two<G: Fn(i32, bool) -> i32>(g: G) -> i32 { g(1, true) }
fn zero<G: Fn() -> i32>(g: G) -> i32 { g() }
#[thrust_macros::requires(y)]
#[thrust_macros::ensures(result == x)]
fn pick(x: i32, y: bool) -> i32 { x }
#[thrust_macros::ensures(result == 7)]
fn seven() -> i32 { 7 }
fn main() { assert!(apply(inc, 4) == 5); assert!(apply1(inc, 4) == 6); assert!(two(pick) == 1); assert!(zero(seven) == 7); assert!(apply(&inc, 4)==5); }
