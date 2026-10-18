//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_manually_drop.rs`: dropping `_t` drops its second component only,
// since the first is inside a `ManuallyDrop`.

use std::mem::ManuallyDrop;

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let _t = (ManuallyDrop::new(Guard(1)), Guard(0));
}
