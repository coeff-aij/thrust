//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
// A function coerced to an `unsafe fn` pointer keeps its function type: the call is checked
// against the callee's contract.
fn f(x: i32) {
    assert!(x > 0);
}

fn main() {
    let p = f as unsafe fn(i32);
    unsafe { p(1) };
}
