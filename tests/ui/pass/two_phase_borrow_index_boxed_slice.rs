//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `a[i].bump(a[i])` on a boxed slice: the read in the argument is redirected to the two-phase
// borrow, and its bounds check stays a check, reading the length through the box.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust_macros::requires(i < a.len())]
fn bump_boxed(mut a: Box<[i64]>, i: usize) {
    let x = a[i];
    a[i].bump(a[i]);
    assert!(a[i] == x + 1);
}

fn main() {}
