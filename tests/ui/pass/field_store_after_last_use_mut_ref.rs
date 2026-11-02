//@check-pass
//@compile-flags: -C debug-assertions=off

// A `&mut` stored into a field of a parameter that is not read afterwards dies with the store, so
// the caller gets its referent back unchanged.

struct A<'a> {
    r: &'a mut i64,
}

fn id<'a>(r: &'a mut i64) -> &'a mut i64 {
    r
}

fn g<'a>(mut a: A<'a>, x: &'a mut i64) {
    *a.r += 1;
    a.r = id(x);
}

fn main() {
    let mut v = 1;
    let mut w = 1;
    g(A { r: &mut w }, &mut v);
    assert!(v == 1 && w == 2);
}
