//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl.rs`: the destructor's assertion holds of every value it may run on.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        if self.0 != 0 {
            self.0 = 0;
        }
        assert!(self.0 == 0);
    }
}

fn main() {
    let _g = Guard(0);
}
