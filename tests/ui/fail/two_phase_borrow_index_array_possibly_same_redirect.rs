//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The receiver `*a[0]` is reserved; the argument re-points `a[j]`, which is `a[0]` when `j == 0`.
// Thrust asserts `j != 0` at the write, and `j == 0` satisfies the precondition.

trait Bump {
    fn bump(&mut self, k: i64);
}

impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

#[thrust_macros::requires(j < 2)]
#[thrust_macros::ensures(true)]
fn go<'a>(a: &mut [&'a mut i64; 2], c: &'a mut i64, j: usize) {
    (*a[0]).bump({
        a[j] = c;
        10
    });
}

fn main() {}
