//@compile-flags: -C debug-assertions=off

// `q` is the temporary of `deref_copy (*x).0`, used once; one branch overwrites `x` before the
// use, which Thrust refuses for a reborrow it cannot tell from a two-phase one.

#[inline(never)]
fn id(x: bool) -> bool {
    x
}

fn main() {
    let mut a = 0;
    let mut b = 0;
    let mut sa = (&mut a, 0);
    let mut sb = (&mut b, 0);
    let mut x = &mut sa;
    let q = &mut *x.0;
    if id(true) {
        x = &mut sb; //~ ERROR: this may change which place a two-phase borrow names
    }
    *q += 1;
    *x.0 += 1;
    x.1 += 1;
    assert!(b == 1);
}
