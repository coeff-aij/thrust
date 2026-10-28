//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_OPTIMIZED_MIR=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=1` and above a constant index reaches MIR as a constant projection
// (`(*_1)[1 of 2]`) instead of an index local.
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).len() > 1 && (*result)[1] == 20
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    slice[1] += 1;
    assert!(slice[1] == 21);
}
