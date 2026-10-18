//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The receiver `deref_copy s.0` of `set` is used in the block after `get` reads `*s.0`.

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
    let mut s = (&mut c, 0);
    s.0.set(s.0.get() + 1);
    s.1 += 1;
    assert!(c.0 == 3);
}
