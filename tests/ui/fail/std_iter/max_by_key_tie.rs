//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
// slow: open: no answer in 60 s (fptprove thrust-benchmarks max_by_key_tie_2026-11-09); max_by_key by default: fail/std_iter/max_by_key.rs, fail/std_iter/max_by_key_state.rs, fail/std_iter/max_by_key_yielded_pre.rs

// Of two items with the greatest key, `max_by_key` returns the last, not the first.
fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(2);
    v.push(3);
    let m = v.into_iter().max_by_key(|x| *x / 2);
    assert!(m == Some(2));
}
