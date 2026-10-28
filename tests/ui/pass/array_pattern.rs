//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An array pattern reads its elements at constant indexes that no bounds check guards
// (`_1[0 of 2]`).
fn swap_pair(a: [i64; 2]) -> [i64; 2] {
    let [x, y] = a;
    [y, x]
}

fn main() {
    let [x, y] = swap_pair([1, 2]);
    assert!(x == 2 && y == 1);
}
