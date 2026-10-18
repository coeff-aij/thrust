//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Dropping `_o` runs `Outer`'s destructor (`a = 5`) and then `Inner`'s (`a + 1`), so `a` is 6,
// not the 5 the other order would leave.

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
    assert!(a == 5);
}
