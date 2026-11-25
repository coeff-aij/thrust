//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The reserved receiver is `s[i][0]`; the argument reads it, then overwrites `s[j]`, which is the
// pointer `s[i]` the receiver goes through when `i == j`. The receiver holds 5, not the 6 checked.
trait Check {
    fn check(&mut self, k: i64);
}

impl Check for i64 {
    fn check(&mut self, k: i64) {
        assert!(*self == k);
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*s).len() && 0 < (*(*s)[i]).len() && (*(*s)[i])[0] == 5 && 0 < (*b).len())]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut [i64]], b: &'a mut [i64], i: usize, j: usize) {
    s[i][0].check({
        let k = s[i][0] + 1;
        s[j] = b;
        k
    });
}

fn main() {}
