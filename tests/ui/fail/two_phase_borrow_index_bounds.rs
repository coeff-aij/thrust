//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The bounds check of `s[5]` runs where `&mut s[5]` is reserved, before the argument, which does
// not return.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

fn spin(_s: &[i64]) -> i64 {
    loop {}
}

#[thrust_macros::requires((*s).len() > 4)]
#[thrust_macros::ensures(true)]
fn f(s: &mut [i64]) {
    s[5].bump(spin(s));
}

fn main() {}
