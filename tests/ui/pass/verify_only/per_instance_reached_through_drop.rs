//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=caller THRUST_PER_INSTANCE_GENERICS=1

// Dropping a `D` at the end of the selected `caller` runs `D`'s `drop`, which calls the
// per-instance `g` at `i64`; its assertion holds there.

#[thrust::callable]
fn g<T: Copy>(x: T) -> T {
    let ok = true;
    assert!(ok);
    x
}

struct D(i64);

impl Drop for D {
    fn drop(&mut self) {
        let _ = g(self.0);
    }
}

#[thrust::callable]
fn caller() {
    let _d = D(3);
}

fn main() {}
