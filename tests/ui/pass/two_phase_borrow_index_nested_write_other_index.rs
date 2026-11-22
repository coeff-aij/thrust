//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The reserved receiver is `s[i][0]` (5). The argument overwrites `s[j]` with `i != j`, so `check` still
// receives the borrow of `s[i][0]`; the write may name the same element, so the creation moves before it.
trait Check {
    fn check(&mut self, k: i64);
}

impl Check for i64 {
    fn check(&mut self, k: i64) {
        assert!(*self == k);
    }
}

#[thrust_macros::requires(i < (*s).len() && i != j && j < (*s).len() && 0 < (*(*s)[i]).len() && (*(*s)[i])[0] == 5 && 0 < (*b).len() && (*b)[0] == 0)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut [i64]], b: &'a mut [i64], i: usize, j: usize) {
    s[i][0].check({
        let k = s[i][0];
        s[j] = b;
        k
    });
}

fn main() {}
