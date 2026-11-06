//@ignore-on-host: draft, six goals of the loop's invariant get no answer (see README.md)
//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::LayoutCalculator::place_fields,rustc_abi::layout::niche_sized,rustc_abi::layout::no_niche_ends_by,rustc_abi::Size::add_assign,rustc_abi::Size::bits,rustc_abi::Size::align_to
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// `univariant_biased`'s field loop, `place_fields` (rewrites.md R19), with its invariant over the
// loop's history, against the contract `univariant_biased` reads it by; `place_field` and the
// lemmas it uses are trusted on their contracts, which the place_field and permutation_sum roots
// verify.
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
