//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::coroutine::coroutine_saved_local_eligibility,rustc_abi::layout::coroutine::make_ineligible,rustc_abi::layout::coroutine::set_assignment,rustc_abi::Size::add_assign,rustc_abi::Size::unsigned_int_max,rustc_abi::TargetDataLayout::obj_size_bound,rustc_abi::Size::bits,rustc_abi::Size::add,rustc_abi::Size::align_to
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Stage 5 of the rustc-coroutine verification target: `coroutine_saved_local_eligibility` of
// rustc_abi's layout/coroutine.rs, with the two helpers that hold its writes to `assignments`.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
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
