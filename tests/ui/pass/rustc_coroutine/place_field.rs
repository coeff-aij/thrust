//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::LayoutCalculator::place_field,rustc_abi::layout::LayoutCalculator::offer_niche,rustc_abi::layout::pow2_mono,rustc_abi::layout::pow2_max,rustc_abi::layout::niche_ends_later,rustc_abi::layout::LayoutCalculator::set_offset,rustc_abi::layout::aligned_within,rustc_abi::layout::pow2_pos,rustc_abi::layout::LayoutCalculator::align_step
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// The body of `univariant_biased`'s field loop after the unsized checks, `place_field`, and its
// niche choice, `offer_niche` (rewrites.md R18), with the lemmas they use, against the contracts
// `univariant_biased` reads them by.
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
