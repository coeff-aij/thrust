//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

fn main() {
    let arr = [1_i64, 2, 3];
    let v: &[i64] = &arr;
    let w = &v[..=1];
    assert!(w.len() == 2);
    assert!(w[1] == 2);
}
