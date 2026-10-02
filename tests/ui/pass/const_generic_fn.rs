//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn identity<T, const N: usize>(array: [T; N]) -> [T; N] {
    array
}

fn main() {
    let arr = identity([1i32, 2, 3]);
    let s: &[i32] = &arr;
    assert!(s[0] == 1);
}
