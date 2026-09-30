//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// The pass version with a broken assertion.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= 32)]
#[thrust::trusted]
fn bits(x: u32) -> u32 {
    let count = |y: u32| y.trailing_zeros();
    count(x)
}

fn main() {
    assert!(bits(8) > 32);
}
