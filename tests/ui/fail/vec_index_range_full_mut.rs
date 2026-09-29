//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

fn main() {
    let mut v = Vec::new();
    v.push(1_i64);
    v.push(2);
    let w = &mut v[..];
    w[1] = 5;
    assert!(v.len() == 2);
    assert!(v[0] == 1);
    assert!(v[1] == 2);
}
