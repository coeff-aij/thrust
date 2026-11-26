//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[i][i].bump(s[i][i])` indexes both levels with `i`: the bounds check of the inner `[i]`,
// against the length of `s[i]`, lies between the check of the outer `[i]` and the borrow, and
// the arguments check `i` again at both levels; each level keeps its own check.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && i < (*(*s)[i]).len())]
fn bump_diagonal(s: &mut [&mut [i64]], i: usize) {
    let x = s[i][i];
    s[i][i].bump(s[i][i]);
    assert!(s[i][i] == x);
}

fn main() {}
