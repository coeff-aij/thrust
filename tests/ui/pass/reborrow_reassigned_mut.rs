//@check-pass
//@compile-flags: -C debug-assertions=off

// A place that a `&mut` is assigned to is reborrowed for a write through it.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*(!x) == 5)]
fn redirect<'a>(x: &mut &'a mut i32, y: &'a mut i32) {
    *x = y;
    **x = 5;
}

fn main() {
    let mut a = 0;
    let mut b = 0;
    let mut r = &mut a;
    *r = 3;
    r = &mut b;
    *r = 5;
    assert!(a == 3);
    assert!(b == 5);
}
