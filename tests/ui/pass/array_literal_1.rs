//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

fn main() {
    let arr = [1i32, 2, 3];
    let s: &[i32] = &arr;
    let v = s[0];
    assert!(v == 1);
}
