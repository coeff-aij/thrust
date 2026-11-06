//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off --cfg thrust_eligibility_fail
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::coroutine::set_assignment,rustc_abi::Size::add_assign,rustc_abi::Size::bits
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Stage 5 of the rustc-coroutine verification target: `coroutine_saved_local_eligibility` of
// rustc_abi's layout/coroutine.rs, with the two helpers that hold its writes to `assignments`.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it. This twin verifies only `set_assignment`, under `cfg(thrust_eligibility_fail)`, which
// adds to its contract that the write gives every local the new value, not only `local`.
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
