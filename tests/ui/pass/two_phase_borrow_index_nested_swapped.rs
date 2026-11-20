//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[i][j].bump(s[j][i])` checks `j` and then `i` against the lengths of both levels; each index
// of the borrow is paired with the check of its own level.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust_macros::requires(
    i < (*s).len() && j < (*s).len() && j < (*(*s)[i]).len() && i < (*(*s)[j]).len()
)]
fn bump_transposed(s: &mut [&mut [i64]], i: usize, j: usize) {
    let y = s[j][i];
    s[i][j].bump(s[j][i]);
    assert!(s[i][j] == y + 1);
}

fn main() {}
