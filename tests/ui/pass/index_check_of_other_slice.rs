//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=1` the bounds check of `s[3]`, whose value is unused, is followed by the
// access `v[3]`, whose check rustc dropped; the check stays the one of `s`.
#[thrust::callable]
fn f(s: &[i64], v: [i64; 10]) -> i64 {
    if s.len() > 3 {
        let _ = s[3];
    }
    v[3]
}
fn main() {}
