//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The reserved place `s[i][0]` is not cut by `s[j] = b` (`i != j`); the argument reads `s.len()`.

trait Bump {
    fn bump(&mut self, k: i64);
}
impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*s).len() && i != j && 0 < (*(*s)[i]).len() && 0 < (*b).len())]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut [i64]], b: &'a mut [i64], i: usize, j: usize) {
    let n = s.len() as i64;
    s[i][0].bump({ s[j] = b; s.len() as i64 });
    assert!(s[i][0] == n + 1);
}
fn main() {}
