//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `drop` writes through the `&mut` that `_w` holds before the borrow ends, so the prophecy is
// resolved to the value `drop` leaves: `a` is 7 at the assertion.

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 7;
    }
}

fn main() {
    let mut a = 0;
    {
        let _w = W(&mut a);
    }
    assert!(a == 0);
}
