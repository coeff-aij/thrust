//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_flag.rs`: `w` is set, and so dropped, only when `c` holds.

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 1;
    }
}

fn cond() -> bool {
    true
}

fn main() {
    let mut a = 0;
    let c = cond();
    {
        let w;
        if c {
            w = W(&mut a);
        }
    }
    assert!(c || a == 0);
    assert!(!c || a == 1);
}
