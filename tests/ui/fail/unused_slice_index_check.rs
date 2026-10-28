//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The bounds check of the unused `s[3]` is still made. Thrust analyzes the MIR of
// `-C opt-level=0` whatever the flag; at `-C opt-level=1` rustc's MIR follows that check, on a
// constant index, by the access `t[3]`.
#[thrust_macros::requires(t.len() > 3)]
#[thrust_macros::ensures(true)]
fn f(s: &[i64], t: &[i64]) -> i64 {
    let _ = s[3];
    t[3]
}
fn main() {}
