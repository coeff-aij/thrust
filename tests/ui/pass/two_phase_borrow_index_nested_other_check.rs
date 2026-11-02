//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The inner index of `a[i][j]` is checked against `c` first, then against `a[i]`; the bounds check
// of the borrow is the one of `a[i]`, and the check of `c` stays.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust_macros::requires(i < 2 && j < 2 && j < (*c).len())]
fn f(c: &[i64], i: usize, j: usize) {
    let mut a = [[1_i64, 2], [3, 4]];
    a[i][{
        let _ = c[j];
        j
    }]
    .bump(a[i][j]);
}

fn main() {
    f(&[0, 0], 0, 1);
}
