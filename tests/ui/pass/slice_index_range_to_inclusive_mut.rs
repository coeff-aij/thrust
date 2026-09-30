//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

fn main() {
    let mut arr = [1_i64, 2, 3];
    let v: &mut [i64] = &mut arr;
    let w = &mut v[..=1];
    w[1] = 5;
    assert!(v.len() == 3);
    assert!(v[1] == 5);
    assert!(v[2] == 3);
}
