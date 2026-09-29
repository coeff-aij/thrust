//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

fn main() {
    let arr = [0i32, 0, 0, 0];
    let s: &[i32] = &arr;
    let _ = s[3];
}
