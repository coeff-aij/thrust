//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A destructor takes no precondition, since Rust runs it wherever a value is dropped, also in
// code Thrust does not analyze: it is checked under `requires(true)`, and `Guard(1)` would panic,
// although `main` drops only `Guard(0)`.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let _g = Guard(0);
}
