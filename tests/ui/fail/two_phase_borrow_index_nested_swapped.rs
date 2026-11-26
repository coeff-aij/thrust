//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[i][j]` and `s[j][i]` index the two levels with swapped locals: a region that runs past a
// check against the other level's slice must still pair each check with its own access, also
// when the value read through `s[j][i]` is passed to a two-phase borrow of `s[i][j]`.
// The bound `i < s[j].len()` is missing, so the read `s[j][i]` can fail.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*s).len() && j < (*(*s)[i]).len())]
fn bump_swapped(s: &mut [&mut [i64]], i: usize, j: usize) {
    let x = s[j][i];
    s[i][j].bump(x);
    assert!(s[i][j] == x + 1);
}

fn main() {}
