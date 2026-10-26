//@ignore-on-host: not yet verifiable, the solver gives no refutation within 300 s (fptprove thrust-benchmarks unsolved/std_iter_map_sum_state_2026-10-25/)
//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// The stateful closure failing on its second call, run by sum over three items.
fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1); v.push(2); v.push(3);
    let mut n = 0u64;
    let s: usize = v.iter().map(|_w| { n += 1; assert!(n <= 1); 1usize }).sum();
}
