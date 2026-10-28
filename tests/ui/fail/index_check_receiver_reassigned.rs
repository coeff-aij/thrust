//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_OPTIMIZED_MIR=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=1` the bounds check of `t[3]` on `s` is followed by `t = w` and the access
// `t[3]`, whose check GVN reduced to the constant length of `w`; the first check stays `s`'s.

#[thrust::callable]
fn f(s: &[i64], w: &[i64; 10]) -> i64 {
    let mut t: &[i64] = s;
    let _ = t[3];
    t = w;
    t[3]
}
fn main() {}
