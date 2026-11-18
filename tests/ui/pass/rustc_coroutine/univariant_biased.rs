//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::LayoutCalculator::univariant_biased,rustc_abi::layout::LayoutCalculator::univariant_biased_place,rustc_abi::layout::LayoutCalculator::fields_ok_of_layout_pre,rustc_abi::layout::LayoutCalculator::univariant_biased_finish,rustc_abi::layout::as_local,case_study::iter::iter_enumerated_trusted,rustc_abi::layout::arbitrary_parts,rustc_abi::layout::placement_ends_within_of,rustc_abi::layout::placement_below_weighs,rustc_abi::layout::arbitrary_of_placed,rustc_abi::layout::dl_of_is,rustc_abi::layout::layout_within_every_dl,rustc_abi::layout::size_below_bound_if_fits,rustc_abi::layout::univariant_biased_post_of_ok,rustc_abi::layout::univariant_biased_post_of_err
//@rustc-env: THRUST_SPLIT=1 THRUST_CALL_RESULT_DIRECT=1
// Stage 6 of the rustc-coroutine verification target: `LayoutCalculator::univariant_biased` of
// rustc_abi's layout.rs, against the contract `univariant` relies on.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage.
// It also selects `univariant_biased_place` (the `place_fields` call, the size check and the `Ok`),
// the lemmas its proof uses (`fields_ok_of_layout_pre`, `placement_ends_within_of`,
// `placement_below_weighs`, `size_below_bound_if_fits`, `dl_of_is`, `layout_within_every_dl`,
// `arbitrary_of_placed`, `univariant_biased_post_of_ok`, `univariant_biased_post_of_err`),
// `univariant_biased_finish`, `as_local`, `iter_enumerated_trusted` of thrust/iter.rs and
// `arbitrary_parts` of layout.rs. `place_fields` and the lemmas the `place_field.rs` root checks are
// trusted on their contracts.
// Each goal of the functions marked `#[thrust::split_goals]` is solved with the clauses it depends
// on, the other goals in their classes.
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
