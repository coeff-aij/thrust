//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn go<const N: usize>() { assert!(N == N); }
fn main() { go::<3>(); }
