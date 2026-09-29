//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

fn main() {
    let mut v = Vec::new();
    v.push(0);
    assert!(v.len() == 0);
}
