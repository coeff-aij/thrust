//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The receiver `*a[0]` is reserved; the argument re-points `a[1]`. The constant indices differ,
// so `a[0]` is unchanged and `bump` runs on `x`.

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
    let mut a: [&mut i64; 2] = [&mut x, &mut y];
    (*a[0]).bump({
        a[1] = &mut c;
        10
    });
    assert!(*a[0] == 11);
}
