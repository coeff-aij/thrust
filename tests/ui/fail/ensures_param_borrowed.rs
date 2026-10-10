//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// In an `ensures`, a `mut` parameter denotes its value at the call, also after the body lends it
// out as `&mut` and the callee changes it.

#[thrust_macros::ensures(!m == *m + 1)]
fn inc(m: &mut i64) {
    *m += 1;
}

#[thrust_macros::ensures(result == x)]
fn incremented(mut x: i64) -> i64 {
    inc(&mut x);
    x
}

fn main() {}
