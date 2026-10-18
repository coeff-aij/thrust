//@check-pass
//@compile-flags: -C debug-assertions=off

// `q` is the temporary of `deref_copy s.0` of a `&i32`, read after one branch overwrites `s.0`.

#[inline(never)]
fn id(x: bool) -> bool {
    x
}

fn main() {
    let a = 1;
    let b = 2;
    let mut s = (&a, 0);
    let q = &*s.0;
    if id(true) {
        s.0 = &b;
    }
    s.1 += *s.0;
    assert!(*q == 1);
}
