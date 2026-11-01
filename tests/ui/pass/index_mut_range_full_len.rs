//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `IndexMut` keeps the length: a `&mut` borrow of the whole vector or slice leaves the final
// sequence as long as the current one, as in Creusot's `index_mut` contract.
fn keep(s: &mut [i64]) {
    let n = s.len();
    let w = &mut s[..];
    assert!(s.len() == n);
}

fn main() {
    let mut v = Vec::new();
    v.push(1_i64);
    v.push(2);
    let w = &mut v[..];
    assert!(v.len() == 2);
    keep(&mut v);
}
