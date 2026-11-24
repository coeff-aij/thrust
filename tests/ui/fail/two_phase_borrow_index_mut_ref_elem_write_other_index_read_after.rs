//@compile-flags: -C debug-assertions=off
// Must be rejected. The receiver `*s[i]` is a `&mut` read out of the slice before the argument,
// which overwrites `s[j]`, which may be `s[i]`, and then reads `*s[i]`. With `i != j` the read is
// of the reserved place, so the reborrow cannot be created before the write; the read must come
// before it, as in `pass/two_phase_borrow_index_mut_ref_elem_write_other_index.rs`.
trait Bump {
    fn bump(&mut self, k: i64);
}

impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*s).len() && i != j)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut i64], b: &'a mut i64, i: usize, j: usize) {
    (*s[i]).bump({
        s[j] = b;
        *s[i] //~ ERROR: after a write that may change which place the borrow names
    });
    assert!(false);
}

fn main() {}
