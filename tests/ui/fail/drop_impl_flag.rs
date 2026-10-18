//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `w` is dropped under its drop flag at the end of its scope, which runs the destructor when `c`
// holds: `a` is 1 then.

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
    assert!(!c || a == 0);
}
