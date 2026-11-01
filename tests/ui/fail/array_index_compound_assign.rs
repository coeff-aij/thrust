//@error-in-other-file: Unsat
//@compile-flags: -C overflow-checks=on -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An array element is read and written through one index across the blocks that the bounds
// check and the overflow assert split.
fn main() {
    let mut a = [1i64, 2, 3];
    let i = 1;
    a[i] += 1;
    a[i] += 1;
    assert!(a[0] == 1);
    assert!(a[1] == 3);
    assert!(a[2] == 3);
}
