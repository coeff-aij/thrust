//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The receiver `*s[i]` is a `&mut` read out of the slice before the argument, which overwrites
// `s[j]` with `i != j`; `bump` gets the reborrow of the old `*s[i]` (5) and the value read before
// the write.

trait Bump {
    fn bump(&mut self, k: i64);
}

impl Bump for i64 {
    fn bump(&mut self, k: i64) {
        *self = k + 1;
    }
}

#[thrust_macros::requires(i < (*s).len() && j < (*s).len() && i != j && *(*s)[i] == 5)]
#[thrust_macros::ensures(true)]
fn go<'a>(s: &mut [&'a mut i64], b: &'a mut i64, i: usize, j: usize) {
    (*s[i]).bump({
        let k = *s[i];
        s[j] = b;
        k
    });
    assert!(*s[i] == 6);
}

fn main() {}
