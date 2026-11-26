//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The iterator a `for` loop's desugaring binds as `iter` is named by no identifier: the
// `assume!` is of the variable `iter` around the loop, which holds, and the assertion fails.
fn main() {
    let iter: std::ops::Range<i64> = 10..20;
    for _i in 0..3i64 {
        thrust_macros::assume!(|iter: std::ops::Range<i64>| iter.start == 10);
        assert!(false);
    }
    let _ = iter;
}
