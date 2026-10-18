//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/drop_impl_std.rs`: `Vec::clear` empties `v`.

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 1;
    }
}

impl thrust_models::Model for W<'_> {
    type Ty = Self;
}

fn main() {
    let mut a = 0;
    let mut v = Vec::new();
    v.push(W(&mut a));
    v.clear();
    let n = v.len();
    std::mem::forget(v);
    assert!(n == 0);
}
