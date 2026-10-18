//@check-pass
//@compile-flags: -C debug-assertions=off

// `two_phase_borrow_method` with the read taken before the borrow.

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
    let g = c.get();
    c.set(g + 1);
    assert!(c.0 == 2);
}
