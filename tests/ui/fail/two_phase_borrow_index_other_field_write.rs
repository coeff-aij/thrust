//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The receiver `*s[i].0` is reserved; the argument writes the other field of another element and
// reads the receiver, which still holds its value before the call.

trait Bump {
    fn bump(&mut self, k: i64);
}

impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*s).len() && i != j && *(*s)[i].0 == 1)]
#[thrust_macros::ensures(true)]
fn go(s: &mut [(&mut i64, i64)], i: usize, j: usize) {
    (*s[i].0).bump({
        s[j].1 = 3;
        *s[i].0
    });
    assert!(*s[i].0 == 1);
}

fn main() {}
