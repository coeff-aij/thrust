//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Swapping two `&mut` through a reborrow: `t = &mut *a`, a `copy a` in the optimized MIR, is
// moved into `b` after `a` is reassigned.

#[thrust_macros::requires(*a == 1 && *b == 2)]
#[thrust_macros::ensures(true)]
fn go<'x>(mut a: &'x mut i64, mut b: &'x mut i64) {
    let t = &mut *a;
    a = b;
    b = t;
    *a += 10;
    *b += 20;
    assert!(*a == 12 && *b == 22);
}

fn main() {}
