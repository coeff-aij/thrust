//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `v.push(v.len())` reads `v` while `&mut v` is reserved.

fn main() {
    let mut v = Vec::new();
    v.push(0);
    v.push(v.len());
    assert!(v.len() == 2);
    assert!(v[1] == 1);
}
