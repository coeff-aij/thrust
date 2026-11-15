//@ignore-on-host: groundwork probe, not counted: parts 41 and 38 of the place body get no answer (see README.md)
//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::LayoutCalculator::univariant_biased_place,rustc_abi::layout::LayoutCalculator::fields_ok_of_layout_pre
//@rustc-env: THRUST_SPLIT=4 THRUST_SPLIT_GOALS=1 THRUST_CALL_RESULT_DIRECT=1
// Probe: the body of `univariant_biased_place` (the `place_fields` call, the size check and the `Ok`)
// and the lemma `fields_ok_of_layout_pre` its call of `place_fields` uses, against the contract the
// `univariant_biased.rs` root trusts. Groundwork: the root does not count it.
// Each goal of the functions marked `#[thrust::split_goals]` is solved with the clauses it depends
// on, the other goals in their classes.
#![feature(new_range_api)]

#[path = "../../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

fn main() {}
