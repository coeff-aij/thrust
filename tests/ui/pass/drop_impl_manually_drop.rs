//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_manually_drop.rs`: dropping `_t` drops its second component.

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
    assert!(b == 1);
}
