//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

fn main() {
    let mut w: Vec<i64> = Vec::new();
    Vec::push(&mut w, 3);
    Vec::push(&mut w, 4);
    let v: Vec<i64> = w.into_iter().collect();
    assert!(v.len() == 3);
    assert!(v[0] == 3 && v[1] == 4);
}
