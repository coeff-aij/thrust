//@ignore-on-host: draft, the step of `map_bound` and `filter_count` get no answer from the solver (README.md)
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::counts,rustc_abi::layout::coroutine::ones_assigned_disjoint,rustc_abi::layout::coroutine::ones_step
// The count of a variant's fields of thrust/counts.rs, which `layout()`'s per-variant closure
// (stage 7) uses and the `layout.rs` root assumes. The code is the module tree under
// tests/rustc_coroutine/; this file selects the lemmas.
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
