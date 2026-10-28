//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_OPTIMIZED_MIR=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=1` the bounds check of an unused `a[2]` precedes a write of the array and the
// access `a[2]`; the check covers that access only if nothing writes the array in between.
#[thrust::callable]
fn g() {
    let mut a = [1i64, 2, 3];
    let _ = a[2];
    a = [7, 8, 9];
    assert!(a[2] == 9);
}
fn main() {}
