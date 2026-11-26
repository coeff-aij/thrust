//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[0].set(s[0].get() + 1)` on a `&mut` held in a slice reads the element's referent before the
// call reborrows it; the read sees the value before the call.

trait Cell {
    fn set(&mut self, v: i64);
    fn get(&self) -> i64;
}

impl Cell for i64 {
    fn set(&mut self, v: i64) {
        *self = v;
    }

    fn get(&self) -> i64 {
        *self
    }
}

#[thrust_macros::requires((*s).len() > 1 && -100 < *(*s)[0] && *(*s)[0] < 100)]
#[thrust_macros::ensures(*(!s)[0] == *(*s)[0] + 1 && *(!s)[1] == *(*s)[1])]
fn bump_first(s: &mut [&mut i64]) {
    let old = s[0].get();
    s[0].set(s[0].get() + 1);
    s[1].set(old);
}

fn main() {}
