//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_assign.rs`: both values `g` holds pass the destructor's assertion.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

fn main() {
    let mut g = Guard(0);
    g = Guard(0);
    let _ = &g;
}
