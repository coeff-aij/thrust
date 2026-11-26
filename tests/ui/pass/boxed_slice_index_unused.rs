//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An element of a boxed slice that is never read: its bounds check stays a check, reading the
// length through the box. The second `a[i]` is a read paired with its own check.

#[thrust_macros::requires(i < a.len())]
#[thrust_macros::ensures(result == a[i])]
fn unused_then_read(a: Box<[i64]>, i: usize) -> i64 {
    a[i];
    a[i]
}

fn main() {}
