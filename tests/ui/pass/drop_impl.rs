//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl.rs`: the destructor's assertion holds.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let _g = Guard(0);
}
