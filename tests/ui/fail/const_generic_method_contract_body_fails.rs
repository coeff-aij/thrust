//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

struct S;
impl thrust_models::Model for S { type Ty = (); }
#[thrust_macros::context]
impl S {
#[thrust_macros::requires((*a)[0] == 5)]
#[thrust_macros::ensures(true)]
fn go<const N: usize>(&self, a: &mut [i64; 2]) { assert!(false); }
}
fn main() { let mut arr = [5i64, 0]; S.go::<0>(&mut arr); }
