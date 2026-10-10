//@ignore-on-host: draft, passes the frontend with `univariant_biased` analysed; its query is about 324 MB, and `univariant_biased` has no contract of its own yet (see README.md)
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1
// Stage 6 of the rustc-coroutine verification target: `LayoutCalculator::univariant` and
// `univariant_biased` of rustc_abi's layout.rs.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
#![feature(custom_inner_attributes)]
#![feature(new_range_api)]
#![thrust::verify_only("rustc_abi::layout::LayoutCalculator")]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

fn main() {}
