//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
// The twin of `pass/unsafe_fn_pointer_call.rs`: the call violates the callee's contract.
fn f(x: i32) {
    assert!(x > 0);
}

fn main() {
    let p = f as unsafe fn(i32);
    unsafe { p(0) };
}
