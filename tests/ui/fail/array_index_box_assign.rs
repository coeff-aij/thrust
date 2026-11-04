//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Assigning to an indexed element that needs drop drops the old value in one block and writes
// in the next.
fn main() {
    let mut a = [Box::new(1i64), Box::new(2)];
    let i = 1;
    a[i] = Box::new(5);
    a[0] = Box::new(7);
    assert!(*a[0] == 7);
    assert!(*a[1] == 2);
}
