//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Dropping `_t` drops its second component, whose destructor sets `b` to 1, and nothing of
// the first, which is inside a `ManuallyDrop`.

use std::mem::ManuallyDrop;

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 1;
    }
}

fn main() {
    let mut a = 0;
    let mut b = 0;
    {
        let _t = (ManuallyDrop::new(W(&mut a)), W(&mut b));
    }
    assert!(b == 0);
}
