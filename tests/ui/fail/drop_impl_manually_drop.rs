//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Dropping `_t` drops its second component, whose destructor panics.

use std::mem::ManuallyDrop;

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let _t = (ManuallyDrop::new(Guard(1)), Guard(1));
}
