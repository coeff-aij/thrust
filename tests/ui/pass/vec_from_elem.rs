//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn main() {
    let v = vec![7i32; 3];
    assert!(v.len() == 3);
    assert!(v[1] == 7);
}
