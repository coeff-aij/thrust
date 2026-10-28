//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An element borrowed mutably as an autoref'd receiver, its argument read before the borrow.
// When the argument reads the sequence after the borrow (`a[i].bump(a[i])`), the index call
// would make the mutable borrow before that read, so such an access is left to rustc's check.
trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

#[thrust::callable]
fn array(i: usize) {
    let mut a = [10i64, 20, 30];
    if i < 3 {
        let t = a[i];
        a[i].bump(t);
        assert!(a[i] == t + 1);
    }
}

#[thrust::callable]
fn slice(s: &mut [i64]) {
    if s.len() > 0 {
        let t = s[0];
        s[0].bump(t);
        assert!(s[0] == t + 1);
    }
}

fn main() {}
