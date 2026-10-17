//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_field.rs`: `Outer`'s destructor runs before the destructor of its
// field, and both write through the same `&mut`.

struct Guard<'a>(&'a mut i32);

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        assert!(*self.0 == 0);
        *self.0 = 2;
    }
}

struct Outer<'a> {
    g: Guard<'a>,
}

impl Drop for Outer<'_> {
    fn drop(&mut self) {
        *self.g.0 = 0;
    }
}

fn main() {
    let mut a = 1;
    {
        let _o = Outer { g: Guard(&mut a) };
    }
    assert!(a == 2);
}
