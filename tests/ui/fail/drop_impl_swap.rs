//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The values `mem::swap` exchanges are dropped at the end of the block, and each destructor
// sets its referent to 1.

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
    assert!(a == 0);
}
