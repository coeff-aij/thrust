//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Assigning to `g` drops the value it held, whose destructor panics.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let mut g = Guard(1);
    g = Guard(0);
    let _ = &g;
}
