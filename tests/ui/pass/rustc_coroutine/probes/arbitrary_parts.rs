//@ignore-on-host: groundwork probe, not counted in the case study: `arbitrary_parts` is checked in the `univariant_biased.rs` root
//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::arbitrary_parts
//@rustc-env: THRUST_SPLIT=1 THRUST_CALL_RESULT_DIRECT=1
// Probe: `arbitrary_parts` of layout.rs alone (the match on a scalar pair's fields), against its
// contract. The `univariant_biased.rs` root selects the same function together with `univariant_biased`.
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
