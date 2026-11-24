//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The argument re-points `s[j]`, which is the `s[i]` the reserved receiver `s[i][0]` goes
// through, and reads `s` only for the length its bounds check compares with: the borrow stays at
// its reservation and bumps the element `s[i]` pointed to before.

trait Bump {
    fn bump(&mut self, k: i64);
}

impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && i == j && 0 < (*(*s)[i]).len() && 0 < (*b).len() && (*b)[0] == 5)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut [i64]], b: &'a mut [i64], i: usize, j: usize) {
    s[i][0].bump({
        s[j] = b;
        10
    });
    assert!(s[i][0] == 11);
}

fn main() {}
