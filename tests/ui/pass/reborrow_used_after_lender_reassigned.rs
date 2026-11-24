//@check-pass
//@compile-flags: -C debug-assertions=off

// The reborrow `q = &mut *x`, a `copy x` in the optimized MIR, is used once, after `x` is
// reassigned: it still borrows what `x` pointed to before.

#[thrust_macros::requires(*x == 0 && *b == 0)]
#[thrust_macros::ensures(true)]
fn go<'a>(mut x: &'a mut i64, b: &'a mut i64) {
    let q = &mut *x;
    x = b;
    *q += 1;
    *x += 2;
    assert!(*x == 2);
}

fn main() {}
