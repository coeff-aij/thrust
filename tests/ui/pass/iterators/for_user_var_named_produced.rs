//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A user's own variable named `produced` in a `for` loop's invariant is that variable, not the
// loop's ghost history: an invariant without `iter` that names it is accepted as before.

fn main() {
    let mut produced: i64 = 0;
    for _i in 0..3i64 {
        thrust_macros::invariant!(|produced: i64| produced >= 0);
        produced += 1;
    }
    assert!(produced >= 0);
}
