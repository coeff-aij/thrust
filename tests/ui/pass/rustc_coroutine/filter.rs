//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::iter::Filter
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// The case study's `Filter` (thrust/iter.rs, rewrites.md R8), which `univariant_biased` and
// `layout()` call: its `next` against the contract that the item it returns is the last the inner
// iterator produced, and its `IteratorSpec` laws.
// The code is the module tree under tests/rustc_coroutine/; this file selects the adapter.
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
