//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `p.set(p.get() + 1)` for a `p: &mut C` that is reassigned later: the reborrow `&mut *p` is a
// `copy p` in the optimized MIR.

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
    let mut a = C(1);
    let mut b = C(5);
    let mut p = &mut a;
    p.set(p.get() + 1);
    p = &mut b;
    p.set(p.get() + 1);
    assert!(a.0 == 2);
    assert!(b.0 == 7);
}
