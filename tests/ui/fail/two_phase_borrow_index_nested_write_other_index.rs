//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Must be rejected. The reserved receiver is `s[i][0]`, an element of the slice `*s[i]` (5); the argument
// overwrites `s[j]` with `b` and `j == i`, so rustc activates the borrow of the old `s[i][0]`,
// not of `b[0]` (0).
trait Check {
    fn check(&mut self, k: i64);
}

impl Check for i64 {
    fn check(&mut self, k: i64) {
        assert!(*self == k);
    }
}

#[thrust_macros::requires(i < (*s).len() && i == j && 0 < (*(*s)[i]).len() && (*(*s)[i])[0] == 5 && 0 < (*b).len() && (*b)[0] == 0)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut [i64]], b: &'a mut [i64], i: usize, j: usize) {
    s[i][0].check({
        let k = s[i][0] - 5;
        s[j] = b;
        k
    });
}

fn main() {}
