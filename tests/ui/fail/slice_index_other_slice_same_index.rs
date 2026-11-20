//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `a[i]` is checked but its element is never used, and `b[i]` follows with the same index: the
// check against `a` keeps guarding `a`, and is not paired with the element of `b`.

#[thrust_macros::requires(i < (*b).len())]
fn statement(a: &[i64], b: &[i64], i: usize) -> i64 {
    a[i];
    b[i]
}

#[thrust_macros::requires(i < (*b).len())]
fn wildcard(a: &[i64], b: &[i64], i: usize) -> i64 {
    let _ = a[i];
    b[i]
}

#[thrust_macros::requires(i < (*b).len())]
fn wildcard_match(a: &[i64], b: &[i64], i: usize) -> i64 {
    match a[i] {
        _ => b[i],
    }
}

fn main() {}
