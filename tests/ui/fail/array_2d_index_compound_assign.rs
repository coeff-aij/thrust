//@error-in-other-file: Unsat
//@compile-flags: -C overflow-checks=on -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An element of a two-dimensional array is read and written through two indexes, constant or
// not, across the blocks that the bounds checks and the overflow assert split.
fn main() {
    let mut a = [[1i64, 2], [3, 4]];
    let i = 1;
    a[0][0] += 1;
    a[i][1] += 1;
    a[1][i] += 1;
    a[i][0] += 1;
    assert!(a[0][0] == 2);
    assert!(a[0][1] == 2);
    assert!(a[1][0] == 4);
    assert!(a[1][1] == 5);
}
