//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Dropping `_o` runs `Outer`'s destructor and then `Guard`'s, which sets `a` to 2.

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
    assert!(a == 1);
}
