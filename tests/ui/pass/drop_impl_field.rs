//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_field.rs`: `Outer`'s destructor runs before the destructor of its
// field, both through the same `&mut`.

struct Inner<'a>(&'a mut i32);

impl Drop for Inner<'_> {
    fn drop(&mut self) {
        *self.0 += 1;
    }
}

struct Outer<'a> {
    g: Inner<'a>,
}

impl Drop for Outer<'_> {
    fn drop(&mut self) {
        *self.g.0 = 5;
    }
}

fn main() {
    let mut a = 0;
    {
        let _o = Outer { g: Inner(&mut a) };
    }
    assert!(a == 6);
}
