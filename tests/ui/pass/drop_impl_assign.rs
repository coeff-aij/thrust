//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_assign.rs`: the assignment drops the value `w` held.

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
    assert!(a == 1);
    let _ = &w;
}
