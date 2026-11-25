//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::forall;

pub enum Tag<T> {
    A(T),
    B,
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|_t: Tag<i64>| result > x))]
fn succ(x: i32) -> i32 {
    x + 1
}

fn main() {}
