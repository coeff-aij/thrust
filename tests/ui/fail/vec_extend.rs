//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

fn append<I: IntoIterator<Item = i64>>(v: &mut Vec<i64>, iter: I) {
    v.extend(iter);
}

fn main() {
    let mut v: Vec<i64> = Vec::new();
    Vec::push(&mut v, 1);
    Vec::push(&mut v, 2);
    append(&mut v, Vec::new());
    assert!(v.len() >= 3);
    assert!(v[1] == 2);
}
