//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

fn to_vec<T, const N: usize>(array: [T; N]) -> Vec<T> {
    array.into()
}

fn main() {
    let v = to_vec([1i32, 2, 3]);
    assert!(v.len() == 3);
    assert!(v[1] == 3);
}
