//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// Under `THRUST_INT_RANGE`, `enumerate` requires that the iterator produce at most `usize::MAX`
// items, which a slice iterator does: its count stays below the length.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f(v: &Vec<i64>) {
    for (i, x) in v.iter().enumerate() {
        assert!(i < v.len());
        let _ = x;
    }
}

fn main() {}
