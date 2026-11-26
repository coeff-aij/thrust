//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// Without `THRUST_SPLIT`, `#[thrust::split_goals]` warns once for the host, not again for each of
// the functions its `block_contract!`s are hoisted into; the hoisted functions also carry the
// host's `#[thrust::reveal]`, and the host is generic and instantiated twice.
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn big(x: i64) -> bool { x > 10 }

    #[thrust_macros::context]
    #[thrust::split_goals]
    #[thrust::reveal]
    #[thrust_macros::requires(true)]
    pub fn host<T: Copy + thrust_models::Model>(t: T) -> i64 {
        let a = thrust_macros::block_contract!(|| -> i64 ensures(big(result)), { 11 });
        let b = thrust_macros::block_contract!(|| -> i64 ensures(big(result)), { 12 });
        a + b
    }

fn main() { let _ = host(1i64); let _ = host(2u8); }
