//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_swap.rs`: `mem::swap` drops neither value, and both are dropped at
// the end of the block.

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
        let mut x = W(&mut a);
        let mut y = W(&mut b);
        std::mem::swap(&mut x, &mut y);
    }
    assert!(a == 1 && b == 1);
}
