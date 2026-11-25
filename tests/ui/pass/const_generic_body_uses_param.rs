//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn go<const N: usize>(a: usize) -> usize { N + a }
fn main() { let r = go::<3>(4); assert!(r == 7); }
