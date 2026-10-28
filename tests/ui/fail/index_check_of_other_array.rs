//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_OPTIMIZED_MIR=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=1` an unused `a[k]` leaves at most its bounds check, followed by the access
// `v[5]`, whose check rustc dropped; that check is `a`'s, not `v`'s.
#[allow(unconditional_panic)]
#[thrust::callable]
fn f(v: [i64; 10]) -> i64 {
    let a = [1i64, 2, 3];
    let _ = a[5];
    v[5]
}
fn main() {}
