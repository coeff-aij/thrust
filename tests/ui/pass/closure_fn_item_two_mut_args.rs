//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// Two &mut arguments passed through an Fn bound.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!a == *b && !b == *a)]
fn sw(a: &mut i32, b: &mut i32) { let t = *a; *a = *b; *b = t; }
fn apply2<G: Fn(&mut i32, &mut i32)>(g: G, a: &mut i32, b: &mut i32) { g(a, b) }
fn main() { let mut x = 1; let mut y = 2; apply2(&sw, &mut x, &mut y); assert!(x == 2 && y == 1); }
