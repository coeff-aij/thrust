//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

fn identity<T, const N: usize>(array: [T; N]) -> [T; N] {
    array
}

fn main() {
    let arr = identity([1i32, 2, 3]);
    let s: &[i32] = &arr;
    assert!(s[0] == 2);
}
