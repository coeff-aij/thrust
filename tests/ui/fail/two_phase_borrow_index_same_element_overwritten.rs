//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The reserved place `*s[i]` is cut by `s[j] = b` with `i == j`; the borrow stays on the old
// referent, and `s[i]` is `b` afterwards.

trait Bump {
    fn bump(&mut self, k: i64);
}
impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}
#[thrust_macros::requires(i < (*s).len() && i == j && *b == 5)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut i64], b: &'a mut i64, i: usize, j: usize) {
    (*s[i]).bump({ s[j] = b; 10 });
    assert!(*s[i] == 11);
}
fn main() {}
