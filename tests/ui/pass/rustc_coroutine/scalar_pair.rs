//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::simple::LayoutData::scalar_pair,case_study::iter::max_by_key,case_study::iter::MaxByKeySpec,crate::drive_max_by_key,rustc_abi::Size::add_assign,rustc_abi::Size::bits,rustc_abi::Niche::available
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// `LayoutData::scalar_pair` of rustc_abi's layout/simple.rs, which `univariant_biased` calls on
// two scalar fields, against the contract the `simple.rs` and `univariant_biased.rs` roots read
// it by, with `Niche::from_scalar` and the local `max_by_key` it calls (rewrites.md R21).
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage.
// Each goal is solved with the clauses it depends on (`THRUST_SPLIT_GOALS`).
#![feature(new_range_api)]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use case_study::iter::max_by_key;

// `max_by_key` on the iterator form `scalar_pair` passes it, a chain of two options, with concrete
// items: the fail twin asserts false after the call, and its refutation shows the code after such
// a call reachable under `max_by_key`'s contract.
#[thrust::callable]
fn drive_max_by_key() {
    let best = max_by_key(
        Some(1u32).into_iter().chain(Some(2u32)),
        thrust_macros::closure!(requires(true), ensures(true), |x: &u32| -> u32 { *x }),
    );
    #[cfg(thrust_scalar_pair_fail)]
    thrust_macros::proof_assert!(|best: Option<u32>| false);
    let _ = best;
}

fn main() {}
