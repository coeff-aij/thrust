//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The values `mem::swap` exchanges are dropped at the end of `main`, and `Guard(1)`'s destructor
// panics.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let mut a = Guard(1);
    let mut b = Guard(0);
    std::mem::swap(&mut a, &mut b);
}
