//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A stateful key closure (captures &mut) failing on its second call, run by max_by_key over three items.
fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1); v.push(2); v.push(3);
    let mut n = 0u64;
    let m = v.iter().max_by_key(|x| { n += 1; assert!(n <= 1); **x });
}
