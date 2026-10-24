//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// std's `find` with a predicate that counts its calls and fails on the second: its `pre!` must
// hold at the state each call starts from, whatever state it ends in.
fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1); v.push(2); v.push(3);
    let mut n = 0u64;
    let mut it = v.iter();
    let m = it.find(|x| { n += 1; assert!(n <= 1); false });
}
