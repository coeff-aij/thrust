//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// A closure in a trusted function is part of its trusted body, so it is not analyzed
// even though it calls a std function that has no specification.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result <= 32)]
#[thrust::trusted]
fn bits(x: u32) -> u32 {
    let count = |y: u32| y.trailing_zeros();
    count(x)
}

fn main() {
    assert!(bits(8) <= 32);
}
