//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A ghost local that only the loop invariant reads stays live up to the loop head, so the
// invariant can name it (as Creusot's `Skip::next` names its snapshot `old_self`).

use thrust_models::Ghost;

fn main() {
    let mut x: i64 = 0;
    let x0 = thrust_macros::ghost!(|x: i64| -> i64 { x });
    while x < 10 {
        thrust_macros::invariant!(|x: i64, x0: Ghost<i64>| x0 <= x && x <= 10);
        x += 1;
    }
    assert!(x == 10);
}
