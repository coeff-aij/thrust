//@ignore-on-host: draft, not run yet (see README.md)
//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::simple::LayoutData::scalar_pair,rustc_abi::Niche::from_scalar,rustc_abi::Scalar::size,case_study::iter::max_by_key,case_study::iter::MaxByKeySpec
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// `LayoutData::scalar_pair` of rustc_abi's layout/simple.rs, which `univariant_biased` calls on
// two scalar fields, against the contract the `simple.rs` and `univariant_biased.rs` roots read
// it by, with `Niche::from_scalar` and the local `max_by_key` it calls (rewrites.md R8).
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

fn main() {}
