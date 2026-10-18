//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A two-phase reborrow through a `&mut` parameter that is reassigned later.

struct C(i32);

impl C {
    fn get(&self) -> i32 {
        self.0
    }

    fn set(&mut self, v: i32) {
        self.0 = v
    }
}

fn bump_then_clear<'a>(mut x: &'a mut C, y: &'a mut C) {
    x.set(x.get() + 1);
    x = y;
    x.set(0);
}

fn main() {
    let mut a = C(1);
    let mut b = C(5);
    bump_then_clear(&mut a, &mut b);
    assert!(a.0 == 3);
    assert!(b.0 == 0);
}
