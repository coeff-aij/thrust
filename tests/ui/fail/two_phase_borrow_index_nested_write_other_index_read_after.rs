//@compile-flags: -C debug-assertions=off

// Must be rejected. The reserved receiver is `s[i][0]`; the argument overwrites `s[j]`, which may
// be `s[i]`, and then reads `s[i][0]`. With `i != j` the read is of the reserved place, so the
// creation of the borrow cannot move before the write; the read must come before it, as in
// `pass/two_phase_borrow_index_nested_write_other_index.rs`.
trait Bump {
    fn bump(&mut self, k: i64);
}

impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*s).len() && i != j && 0 < (*(*s)[i]).len() && 0 < (*b).len())]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut [i64]], b: &'a mut [i64], i: usize, j: usize) {
    s[i][0].bump({
        s[j] = b;
        s[i][0] //~ ERROR: after a write that may change which place the borrow names
    });
    assert!(false);
}

fn main() {}
