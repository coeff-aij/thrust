//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[i][j].bump(s[i][j])` reads `s` while `&mut s[i][j]` is reserved, and the bounds check of
// `[j]` reads the length of the reserved `s[i]`; the reads see the value before the call.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*(*s)[i]).len())]
fn bump_same(s: &mut [&mut [i64]], i: usize, j: usize) {
    let x = s[i][j];
    s[i][j].bump(s[i][j]);
    assert!(s[i][j] == x);
}

fn main() {
    let mut a = [[1, 2], [3, 4]];
    a[0][1].bump(a[1][0]);
    assert!(a[0][1] == 4 && a[1][0] == 3);
}
