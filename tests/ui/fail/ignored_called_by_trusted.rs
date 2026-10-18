//@error-in-other-file: is `#[thrust::ignored]`
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A verified body that runs an ignored function.

#[thrust::ignored]
fn helper(x: i32) -> i32 {
    x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t(x: i32) -> i32 {
    helper(x)
}

fn main() {
    let _ = t(1);
}
