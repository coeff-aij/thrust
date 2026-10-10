//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// In an `ensures`, a `mut` parameter denotes its value at the call, not the one the body leaves.

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == 2 * n)]
fn double(mut n: i64) -> i64 {
    let mut r = 0;
    while n > 0 {
        r += 2;
        n -= 1;
    }
    r
}

fn main() {}
