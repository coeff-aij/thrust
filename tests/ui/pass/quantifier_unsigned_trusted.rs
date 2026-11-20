//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A trusted `ensures` quantifying over `u64` is assumed with its variable `>= 0`, so it states
// what it says of Rust values: `result <= n` for every `u64` `n` makes `result` zero.
use thrust_models::forall;

#[thrust::trusted]
#[thrust_macros::ensures(forall(|n: u64| result <= n))]
fn least_u64() -> u64 {
    0
}

fn main() {
    let r = least_u64();
    assert!(r == 0);
}
