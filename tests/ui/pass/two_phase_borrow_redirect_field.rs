//@check-pass
//@compile-flags: -C debug-assertions=off

// The reserved place `(*p).0` outlives the overwrite of `p`; the read after it is of the new place.

struct C(i32);

impl C {
    fn get(&self) -> i32 {
        self.0
    }

    fn set(&mut self, v: i32) {
        self.0 = v
    }
}

struct P(C, i32);

fn main() {
    let mut a = P(C(1), 0);
    let mut b = P(C(5), 0);
    let mut p = &mut a;
    p.0.set({
        p = &mut b;
        p.0.get() + 1
    });
    assert!(a.0 .0 == 6);
    assert!(b.0 .0 == 5);
}
