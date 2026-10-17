//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// Under `THRUST_INT_RANGE`, `enumerate` requires that the iterator produce at most `usize::MAX`
// items, which a slice iterator does: its count stays below the length.
// Fail twin: the body is reached, so the precondition holds and the contract is not vacuous.
// (PCSat gives no answer in 120 s on `i + 1 < v.len()` or `i != 0`.)

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f(v: &Vec<i64>) {
    for (i, x) in v.iter().enumerate() {
        assert!(false);
        let _ = x;
    }
}

fn main() {}
