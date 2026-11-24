//@compile-flags: -C debug-assertions=off

// The argument overwrites `s[j]`, which may be the `s[i]` the reserved receiver `s[i][0]` goes
// through, between the reservation and the activation.

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
        s[j] = b; //~ ERROR: this may change which place a mutable borrow names
        k
    });
}

fn main() {}
