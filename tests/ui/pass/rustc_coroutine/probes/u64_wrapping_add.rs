//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=crate

// The case study's `u64::wrapping_add` spec (thrust/std_specs.rs), which `Hash64::wrapping_add`
// calls: a sum past `u64::MAX` wraps, a small one does not. `Hash64::wrapping_add` itself is
// `#[thrust::callable]`, so its callers see no result; the spec is checked here directly.
#![feature(new_range_api)]

#[path = "../../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn add(a: u64, b: u64) {
    if a == u64::MAX && b == 2 {
        assert!(a.wrapping_add(b) == 1);
    }
    if a <= 100 && b <= 100 {
        assert!(a.wrapping_add(b) == a + b);
    }
}

fn main() {}
