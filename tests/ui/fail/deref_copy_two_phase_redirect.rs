//@compile-flags: -C debug-assertions=off

// The argument overwrites `s.0`, which the receiver `*s.0` of `set` goes through, between the
// reservation and the activation.

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
    let mut b = C(10);
    let mut s = (&mut a, 0);
    s.0.set({
        let x = s.0.get();
        s.0 = &mut b; //~ ERROR: this may change which place a two-phase borrow names
        x + 1
    });
    s.1 += 1;
    assert!(b.0 == 10);
}
