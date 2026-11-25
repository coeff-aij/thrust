//@check-pass
//@compile-flags: -C debug-assertions=off

// A `&mut` the program no longer uses is read at its value at its last use, though its lender
// is written since.
fn main() {
    let mut a: i64 = 1;
    let r = &mut a;
    *r = 2;
    a = 3;
    thrust_macros::proof_assert!(|r: &mut i64| *r == 2);
    assert!(a == 3);
}
