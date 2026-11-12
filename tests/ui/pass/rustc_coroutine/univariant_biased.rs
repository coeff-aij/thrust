//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::LayoutCalculator::univariant_biased,rustc_abi::layout::LayoutCalculator::backend_repr_of,rustc_abi::layout::LayoutCalculator::univariant_biased_finish,case_study::iter::map_new_assumed,case_study::assumed_requires::filter_new_assumed,case_study::assumed_requires::filter_next_assumed,case_study::assumed_requires::map_or_assumed,case_study::assumed_requires::map_assumed,case_study::assumed_requires::sort_by_key_assumed,rustc_abi::layout::as_local,case_study::iter::iter_enumerated_trusted
//@rustc-env: THRUST_SPLIT=1 THRUST_CALL_RESULT_DIRECT=1
// Stage 6 of the rustc-coroutine verification target: `LayoutCalculator::univariant_biased` of
// rustc_abi's layout.rs, against the contract `univariant` relies on.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage.
// It also selects the fallback's wrappers in thrust/iter.rs (`map_new_assumed`) and
// thrust/assumed_requires.rs, so that their bodies are checked, `univariant_biased_finish`,
// `as_local` and `iter_enumerated_trusted` of thrust/iter.rs; `univariant_biased_place` (the `place_fields` call, the size check and
// the `Ok`) is trusted on its contract.
// Each goal of the functions marked `#[thrust::split_goals]` is solved with the clauses it depends
// on, the other goals in their classes.
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
