//@ignore-on-host: draft, as the pass root (README.md)
//@error-in-other-file: Unsat
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens --cfg thrust_layout_fail
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::coroutine::layout,rustc_abi::layout::coroutine::bit_iter_yields_below,rustc_abi::layout::coroutine::index_is_only,rustc_abi::layout::coroutine::layouts_wf_of_entries,rustc_abi::layout::coroutine::layout_pre_of_wf,rustc_abi::layout::coroutine::promote_locals,rustc_abi::layout::coroutine::split_prefix_fields,rustc_abi::layout::coroutine::split_in_memory_order,rustc_abi::layout::coroutine::combine_offsets,rustc_abi::layout::coroutine::variant_field_layouts,rustc_abi::layout::coroutine::variant_layout,rustc_abi::layout::coroutine::variant_env_of,rustc_abi::layout::coroutine::variant_entries_of,rustc_abi::layout::coroutine::variant_promoted_of,rustc_abi::layout::coroutine::ineligible_below_of,case_study::iter,case_study::counts::filter_count,case_study::counts::filter_selects,case_study::counts::map_inner_len,case_study::counts::filter_yields_below
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// The fail twin of the stage 7 root: property 3 at the promoted fields (`ineligible_promoted`) is
// `true`, so that the `unwrap` of an `Ineligible` local's field index is refuted. The code is the module tree
// under tests/rustc_coroutine/; the cfg is read in layout/coroutine.rs.
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
