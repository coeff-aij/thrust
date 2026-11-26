//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The reserved place `*s[i].0` is not cut by `s[j].0 = b` (`i != j`); the argument reads the other
// field `s[i].1`.

trait Bump {
    fn bump(&mut self, k: i64);
}
impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*s).len() && i != j && *(*s)[i].0 == 1 && (*s)[i].1 == 4)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [(&'a mut i64, i64)], b: &'a mut i64, i: usize, j: usize) {
    (*s[i].0).bump({ s[j].0 = b; s[i].1 });
    assert!(*s[i].0 == 6);
}
fn main() {}
