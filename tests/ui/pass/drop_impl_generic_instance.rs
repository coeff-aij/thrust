//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/drop_impl_generic_instance.rs`: a value inside a `ManuallyDrop` is never
// dropped, so `consume`'s contract holds at this instance.

use std::mem::ManuallyDrop;

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn consume<T>(_x: T) {}

fn main() {
    consume(ManuallyDrop::new(Guard(1)));
}
