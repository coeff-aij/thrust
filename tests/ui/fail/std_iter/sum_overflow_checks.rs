//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -C overflow-checks=on
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// With overflow checks on, core's `sum` panics past `usize::MAX`; std.rs gives it no specification
// then, so its call must be unreachable.
fn main() {
    let mut v: Vec<usize> = Vec::new();
    v.push(usize::MAX);
    v.push(1);
    let _s: usize = v.into_iter().sum();
}
