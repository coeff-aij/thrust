//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `a[i];` checks `a[i]` but never uses the element, and `b[i]` follows
// with the same index: the check against `a` keeps guarding `a`, and is not paired with the
// element of `b`.

#[thrust_macros::requires(i < (*a).len() && i < (*b).len())]
fn f(a: &[i64], b: &[i64], i: usize) -> i64 {
    a[i];
    b[i]
}

fn main() {}
