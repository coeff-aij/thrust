//@check-pass
//@compile-flags: -C debug-assertions=off

// `c.set(c.get() + 1)` reserves `&mut c` before `c.get()` reads `c`; the read sees the value
// before the call.

struct C(i32);

impl C {
    fn get(&self) -> i32 {
        self.0
    }

    fn set(&mut self, v: i32) {
        self.0 = v
    }
}

fn main() {
    let mut c = C(1);
    c.set(c.get() + 1);
    assert!(c.0 == 2);
}
