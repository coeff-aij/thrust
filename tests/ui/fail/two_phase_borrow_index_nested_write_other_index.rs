//@compile-flags: -C debug-assertions=off

// The reserved receiver is `s[i][0]`; the argument overwrites `s[j]`, which may be the pointer
// `s[i]` the receiver goes through, before the call activates the borrow. Thrust refuses the write.
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
        s[j] = b; //~ ERROR: this write may change which place a two-phase mutable borrow names
        k
    });
}

fn main() {}
