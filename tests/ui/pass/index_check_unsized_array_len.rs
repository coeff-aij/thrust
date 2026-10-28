//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_OPTIMIZED_MIR=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=1` GVN folds the length of `s`, unsized from a `&[i64; 10]`, to 10.
#[thrust::callable]
fn f(w: &[i64; 10], i: usize) -> i64 {
    let s: &[i64] = w;
    if i < 10 { s[i] } else { 0 }
}
fn main() {}
