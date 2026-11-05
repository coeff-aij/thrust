//@ignore-on-host: diagnostic of the fallback branch, run part by part (see the pass root)
//@error-in-other-file: Unsat
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off --cfg thrust_ub_reach="iter_all"
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::LayoutCalculator::univariant_biased
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// A reachability twin of the fallback's `univariant_biased.rs`: with `cfg(thrust_ub_reach = "iter_all")`
// `univariant_biased` asserts `false` right after the assumptions at that point, so the twin is
// refuted only if the point is reachable under the assumptions before it.
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
