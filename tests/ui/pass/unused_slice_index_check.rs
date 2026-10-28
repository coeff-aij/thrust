//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/unused_slice_index_check.rs`.
#[thrust_macros::requires(s.len() > 3 && t.len() > 3)]
#[thrust_macros::ensures(true)]
fn f(s: &[i64], t: &[i64]) -> i64 {
    let _ = s[3];
    t[3]
}
fn main() {}
