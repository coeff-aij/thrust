//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_OPTIMIZED_MIR=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=1` the bounds check of `t[3]` on the parameter `t` stays `t`'s old slice's,
// although `t = a` follows it before the access `t[3]`.
#[thrust::callable]
fn f<'a>(mut t: &'a [i64], a: &'a [i64; 10]) -> i64 {
    if t.len() > 3 {
        let _ = t[3];
    }
    t = a;
    t[3]
}
fn main() {}
