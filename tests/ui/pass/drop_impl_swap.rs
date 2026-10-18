//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_swap.rs`: `mem::swap` drops neither value, and both pass the
// destructor's assertion when they are dropped.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let mut a = Guard(0);
    let mut b = Guard(0);
    std::mem::swap(&mut a, &mut b);
}
