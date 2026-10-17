//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A value of a type with a `Drop` impl runs `drop` where it is dropped: `_g` panics at the end of
// `main`.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let _g = Guard(1);
}
