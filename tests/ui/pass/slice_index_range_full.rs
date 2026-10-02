//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn main() {
    let arr = [1_i64, 2, 3];
    let v: &[i64] = &arr;
    let w = &v[..];
    assert!(w.len() == 3);
    assert!(w[2] == 3);
}
