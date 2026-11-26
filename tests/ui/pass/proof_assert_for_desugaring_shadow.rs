//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The iterator a `for` loop's desugaring binds as `iter` is named by no identifier: `iter` in the
// body is the variable of that name around the loop.
fn main() {
    let iter: std::ops::Range<i64> = 10..20;
    for _i in 0..3i64 {
        thrust_macros::proof_assert!(|iter: std::ops::Range<i64>| iter.start == 10);
    }
    let _ = iter;
}
