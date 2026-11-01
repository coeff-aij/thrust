//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `s[0].bump(s[0])` reads `s` while `&mut s[0]` is reserved; the read sees the value before the
// call. The same for an array indexed in place.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust_macros::requires((*s).len() > 1)]
#[thrust_macros::ensures(true)]
fn same(s: &mut [i64]) {
    let x = s[0];
    s[0].bump(s[0]);
    assert!(s[0] == x);
}

#[thrust_macros::requires((*s).len() > 1)]
#[thrust_macros::ensures(true)]
fn other(s: &mut [i64]) {
    s[0].bump(s[1]);
    assert!(s[0] == s[1] + 1);
}

fn main() {
    let mut a = [1, 2, 3];
    a[0].bump(a[0]);
    a[1].bump(a[2]);
    assert!(a[0] == 2 && a[1] == 4);
}
