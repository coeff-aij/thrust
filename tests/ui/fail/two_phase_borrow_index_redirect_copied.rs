//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The reserved place `*s[i]` is cut by `s[i] = b`, then `bump` writes the old referent: `s[i]` is `b`.

trait Bump {
    fn bump(&mut self, k: i64);
}
impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}
#[thrust_macros::requires(i < (*s).len() && *b == 5 && *(*s)[i] == 1)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut i64], b: &'a mut i64, i: usize) {
    (*s[i]).bump({ s[i] = b; 10 });
    assert!(*s[i] == 11);
}
fn main() {}
