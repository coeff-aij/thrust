#![feature(custom_inner_attributes)]
#![thrust::verify_only("crate")]

mod spec;

#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result > x)]
fn g(x: i64) -> i64 {
    spec::f(x) + 1
}

fn main() {
    assert!(g(1) > 1);
}
