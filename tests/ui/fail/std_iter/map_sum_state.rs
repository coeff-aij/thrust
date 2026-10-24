//@ignore-on-host: unsound until the fix of issues/2026-10-25-fnmut-pre-final-equals-current.md (thrust-research) is merged: verifies
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
