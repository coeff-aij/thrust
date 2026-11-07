//@ignore-on-host: draft, passes the frontend; its query is beyond what the solver answers (see README.md)
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::LayoutCalculator::univariant_biased,case_study::iter::map_new_assumed,case_study::iter::max_assumed,case_study::iter::filter_new_assumed,case_study::iter::filter_next_assumed,case_study::iter::iter_all_assumed,case_study::iter::map_or_assumed,case_study::iter::map_assumed
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Stage 6 of the rustc-coroutine verification target: `LayoutCalculator::univariant_biased` of
// rustc_abi's layout.rs, against the contract `univariant` relies on.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage.
// It also selects the fallback's wrappers in thrust/iter.rs, so that their bodies are checked.
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
