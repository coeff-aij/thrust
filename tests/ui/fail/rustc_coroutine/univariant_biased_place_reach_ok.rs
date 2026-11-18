//@ignore-on-host: a vacuity check, run by hand; its result is in README.md
//@error-in-other-file: Unsat
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off --cfg 'thrust_univariant_biased_place_reach="ok"'
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::LayoutCalculator::univariant_biased_place
//@rustc-env: THRUST_SPLIT=1 THRUST_CALL_RESULT_DIRECT=1
// A reachability twin of `univariant_biased.rs`'s proof of `univariant_biased_place`: with
// `cfg(thrust_univariant_biased_place_reach = "ok")` the function asserts `false` at the `Ok` return,
// so the twin is refuted only if that point is reachable under the premises before it. Only
// `univariant_biased_place` is selected; the lemmas and `place_fields` it calls are on their contracts.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage.
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
