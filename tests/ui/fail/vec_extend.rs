//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

fn main() {
    let mut v: Vec<i64> = Vec::new();
    Vec::push(&mut v, 1);
    Vec::push(&mut v, 2);
    let mut w: Vec<i64> = Vec::new();
    Vec::push(&mut w, 3);
    v.extend(w);
    assert!(v.len() == 4);
    assert!(v[1] == 2 && v[2] == 3);
}
