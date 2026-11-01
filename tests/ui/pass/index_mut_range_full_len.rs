//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `&mut` slice taken from a vector or a slice keeps its length, whatever the callee does with it
// (Creusot's `index_mut` contract `(^self)@.len() == self@.len()`): through `[..]` and through
// `deref_mut`. The callee is opaque, so the final value of the borrow is open.
#[thrust::trusted]
#[thrust::callable]
fn opaque(_x: &mut [i64]) {}

fn keep(s: &mut [i64]) {
    let n = s.len();
    opaque(&mut s[..]);
    assert!(s.len() == n);
}

fn main() {
    let mut v = Vec::new();
    v.push(1_i64);
    v.push(2);
    opaque(&mut v[..]);
    assert!(v.len() == 2);
    opaque(&mut v);
    assert!(v.len() == 2);
    keep(&mut v);
}
