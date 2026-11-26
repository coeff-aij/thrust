//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An element of a boxed slice that is never read: its bounds check stays a check, reading the
// length through the box. The second `a[i]` is a read paired with its own check.
// The bound `i < a.len()` is missing, so the unused `a[i]` can fail.

#[thrust_macros::requires(0 < 1)]
#[thrust_macros::ensures(result == a[i])]
fn unused_then_read(a: Box<[i64]>, i: usize) -> i64 {
    a[i];
    a[i]
}

fn main() {}
