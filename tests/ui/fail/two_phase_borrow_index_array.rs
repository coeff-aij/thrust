//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `a[0].bump(a[0])` on an array indexed in place reads `a` while `&mut a[0]` is reserved; the
// read sees the value before the call.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

fn main() {
    let mut a = [1, 2, 3];
    a[0].bump(a[0]);
    a[1].bump(a[2]);
    assert!(a[0] == 1 && a[1] == 4);
}
