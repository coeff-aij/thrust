//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

fn main() {
    let v = [1i64, 5, 3];
    if let Some(x) = v.iter().find(|x| **x > 4) {
        assert!(*x == 5);
    }
}
