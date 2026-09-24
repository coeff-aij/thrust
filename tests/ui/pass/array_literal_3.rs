//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

fn main() {
    let mut arr = [1i32, 2, 3];
    let s: &mut [i32] = &mut arr;
    s[0] = 42;
    assert!(s[0] == 42);
    assert!(s[1] == 2);
}
