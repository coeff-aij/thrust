//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Assigning to `w` drops the value it held, whose destructor sets `a` to 1.

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 1;
    }
}

fn main() {
    let mut a = 0;
    let mut b = 0;
    let mut w = W(&mut a);
    w = W(&mut b);
    assert!(a == 0);
    let _ = &w;
}
