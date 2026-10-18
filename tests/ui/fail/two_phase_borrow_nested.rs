//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The two-phase borrow of `d` is reserved and activated while the one of `c` is reserved.

struct C(i32);

impl C {
    fn get(&self) -> i32 {
        self.0
    }

    fn add(&mut self, v: i32) -> i32 {
        self.0 += v;
        self.0
    }

    fn set(&mut self, v: i32) {
        self.0 = v
    }
}

fn main() {
    let mut c = C(1);
    let mut d = C(2);
    c.set(c.get() + d.add(d.get()));
    assert!(c.0 == 6);
    assert!(d.0 == 4);
}
