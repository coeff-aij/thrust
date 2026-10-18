//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_called_by_trusted.rs`: a trusted body is not verified and may run an
// ignored function, as Verus's `external_body` and Creusot's and Prusti's `#[trusted]` may.

#[thrust::ignored]
fn helper(x: i32) -> i32 {
    x
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t(x: i32) -> i32 {
    helper(x)
}

fn main() {
    let _ = t(1);
}
