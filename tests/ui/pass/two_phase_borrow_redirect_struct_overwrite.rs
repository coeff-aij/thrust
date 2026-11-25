//@check-pass
//@compile-flags: -C debug-assertions=off

// The reserved place `*p.0` outlives the overwrite of the whole `p`; the read after it is of the
// new place `b`, and `bump` borrows `a`.

trait Bump {
    fn bump(&mut self, k: i64);
}
impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

fn main() {
    let mut a: i64 = 1;
    let mut b: i64 = 5;
    let mut p = (&mut a, 0i64);
    (*p.0).bump({ p = (&mut b, 1); *p.0 });
    assert!(a == 6);
}
