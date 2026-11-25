//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The pointer the reserved place goes through is overwritten before the activation, after the
// reserved place is read.

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
    p.set({
        let x = p.get();
        p = &mut b;
        x + p.get()
    });
    assert!(a.0 == 10);
    assert!(b.0 == 5);
}
