//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The receiver `*a[0]` is reserved; the argument re-points `a[k]`, which is `a[0]` when `k == 0`.
// The borrow stays on `x`, and `a[0]` is `c` afterwards.

trait Bump {
    fn bump(&mut self, k: i64);
}

impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

fn main() {
    let mut x: i64 = 1;
    let mut y: i64 = 2;
    let mut c: i64 = 7;
    let k: usize = 0;
    let mut a: [&mut i64; 2] = [&mut x, &mut y];
    (*a[0]).bump({
        a[k] = &mut c;
        10
    });
    assert!(*a[0] == 7);
}
