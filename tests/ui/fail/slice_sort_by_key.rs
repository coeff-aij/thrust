//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin asserting the sorted order, which the specification does not state.

fn main() {
    let mut v: Vec<i64> = Vec::new();
    v.push(2);
    v.push(1);
    v.sort_by_key(|x| *x);
    assert!(v.len() == 2);
    assert!(v[0] == 1);
}
