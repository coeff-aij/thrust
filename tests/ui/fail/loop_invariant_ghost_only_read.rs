//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The twin of `pass/loop_invariant_ghost_only_read.rs`: the invariant bounds `x` by the ghost
// `x0` from above, which the first iteration breaks.

use thrust_models::Ghost;

fn main() {
    let mut x: i64 = 0;
    let x0 = thrust_macros::ghost!(|x: i64| -> i64 { x });
    while x < 10 {
        thrust_macros::invariant!(|x: i64, x0: Ghost<i64>| x <= x0);
        x += 1;
    }
    assert!(x == 10);
}
