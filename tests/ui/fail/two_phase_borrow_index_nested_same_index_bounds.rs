//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[i][i].bump(s[i][i])` where only the outer `[i]` is known to be in bounds: the bounds
// check of the inner `[i]`, against the length of `s[i]`, can fail.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust_macros::requires(i < (*s).len())]
fn bump_diagonal(s: &mut [&mut [i64]], i: usize) {
    s[i][i].bump(s[i][i]);
}

fn main() {}
