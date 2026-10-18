//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted body reads a static; the ignored check does not follow static initializers.

static X: i32 = 5;

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 5)]
fn t() -> i32 {
    X
}

fn main() {
    assert!(t() == 5);
}
