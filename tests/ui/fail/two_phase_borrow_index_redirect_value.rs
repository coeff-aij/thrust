//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The reserved place `*s[i]` is cut by `s[i] = b`; the read after it is of `b`.

trait Bump {
    fn bump(&mut self, k: i64);
}
impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}
#[thrust_macros::requires(i < (*s).len() && *b == 5)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut i64], b: &'a mut i64, i: usize) {
    let v = { (*s[i]).bump({ s[i] = b; *s[i] }); *s[i] };
    assert!(v == 6);
}
fn main() {}
