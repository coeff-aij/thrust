//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A function item taking a &mut argument, called through an Fn bound in an analyzed body.

#[thrust_macros::requires(*x < 10)]
#[thrust_macros::ensures(!x == *x + 1)]
fn bump(x: &mut i32) { *x += 1; }
fn apply<G: Fn(&mut i32)>(g: G, r: &mut i32) { g(r) }
fn main() { let mut a = 0; apply(bump, &mut a); assert!(a == 1); }
