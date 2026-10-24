//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// As the fail twin, without the `assert!`.
fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1); v.push(2); v.push(3);
    let mut n = 0u64;
    let mut it = v.iter();
    let m = it.find(|x| { n += 1; false });
}
