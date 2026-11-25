//@check-pass
//@compile-flags: -C debug-assertions=off

// The reborrow `old = &mut *c.0` is no two-phase borrow: it is used after `c.0` is re-pointed
// and the other field is written, and still borrows what `c.0` pointed to before.

#[thrust_macros::requires(*(*c).0 == 1 && *next == 5 && (*c).1 == 0)]
#[thrust_macros::ensures(true)]
fn go<'a>(c: &mut (&'a mut i64, i64), next: &'a mut i64) {
    let old = &mut *c.0;
    c.0 = next;
    c.1 += 1;
    *old += 1;
    assert!(*c.0 == 5 && c.1 == 1);
}

fn main() {}
