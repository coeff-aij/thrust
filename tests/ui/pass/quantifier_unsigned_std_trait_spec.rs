//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The specification of another crate's trait method is read over Rust values: the standard
// library's impls are not checked against it.
use thrust_models::forall;

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(forall(|n: u64| result <= n))]
fn _extern_spec_hasher_finish<H>(h: &H) -> u64
where
    H: std::hash::Hasher + thrust_models::Model,
{
    std::hash::Hasher::finish(h)
}

#[thrust::callable]
fn finish_is_zero<H: std::hash::Hasher + thrust_models::Model>(h: &H) {
    let r = h.finish();
    assert!(r == 0);
}
