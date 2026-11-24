//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::shl_is_pow2,rustc_abi::layout::sum_occurring_step,rustc_abi::layout::sum_occurring_none,rustc_abi::layout::sum_at_last,rustc_abi::layout::sum_at_occurring_last,rustc_abi::layout::sum_at_occurring,rustc_abi::layout::sum_occurring_le,rustc_abi::layout::sum_at_le,rustc_abi::layout::pow2_mono,rustc_abi::layout::bytes_within,rustc_abi::layout::aligned_within,rustc_abi::layout::pow2_pos,rustc_abi::layout::no_niche_ends_by,rustc_abi::layout::niche_ends_later,rustc_abi::layout::niche_sized,rustc_abi::layout::LayoutCalculator::offer_niche,rustc_abi::layout::LayoutCalculator::place_field,rustc_abi::layout::LayoutCalculator::place_fields
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Generated root: the call graph of `layout()` reaches the functions of row univariant_biased in module(s) listed below; see README.md.
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
