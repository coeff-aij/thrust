//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// std's `filter` collected into a `Vec`: every collected item is one the predicate accepted.
// Fail twin: the predicate has a precondition, which `filter` does not allow (as in Creusot).

fn main() {
    let c = thrust_macros::closure!(
        requires(*x >= 0),
        ensures(result == (*x >= 5)),
        |x: &i64| -> bool { *x >= 5 },
    );
    let v: Vec<i64> = (0..10).filter(c).collect();
    if v.len() > 0 {
        assert!(v[0] >= 5);
    }
}
