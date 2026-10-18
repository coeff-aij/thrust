// The contract `arith` verifies, given to this crate as the spec of a function of another crate.
#[thrust::extern_spec_fn]
#[thrust_macros::requires(x >= 0)]
#[thrust_macros::ensures(result > x)]
fn _extern_spec_inc(x: i64) -> i64 {
    arith::inc(x)
}

fn main() {
    assert!(arith::inc(1) > 1);
}
