//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_PER_INSTANCE_GENERICS=1

// The twin of `fail/drop_impl_generic_destructor.rs`: the destructor's assertion holds of every
// value it may run on.

struct G<T> {
    n: i32,
    t: T,
}

impl<T> Drop for G<T> {
    fn drop(&mut self) {
        if self.n != 0 {
            self.n = 0;
        }
        assert!(self.n == 0);
    }
}

impl<T> thrust_models::Model for G<T> {
    type Ty = Self;
}

fn main() {
    let mut v = Vec::new();
    v.push(G { n: 1, t: 0u8 });
    v.clear();
    std::mem::forget(v);
}
