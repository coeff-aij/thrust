//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/drop_impl_generic.rs`: `consume`'s contract says nothing of `a`, and the
// program asserts nothing of it.

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 1;
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn consume<T>(_x: T) {}

fn main() {
    let mut a = 0;
    let b = 0;
    consume(W(&mut a));
    assert!(b == 0);
}
