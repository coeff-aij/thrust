//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::coroutine::index_is_only,rustc_abi::layout::coroutine::bit_iter_yields_below,rustc_abi::layout::coroutine::assigned_count_of,rustc_abi::layout::coroutine::assigned_cnt_le,rustc_abi::layout::coroutine::assigned_entry_counted,rustc_abi::layout::coroutine::combine_wf_of,rustc_abi::layout::coroutine::assigned_here_at,rustc_abi::layout::coroutine::assigned_before_start,rustc_abi::layout::coroutine::assigned_before_take,rustc_abi::layout::coroutine::assigned_before_skip,rustc_abi::layout::coroutine::combine_offsets,rustc_abi::layout::coroutine::promote_locals,rustc_abi::layout::coroutine::split_prefix_fields,rustc_abi::layout::coroutine::layouts_wf_of_entries,rustc_abi::layout::coroutine::layout_pre_of_wf,rustc_abi::layout::coroutine::variant_env_of,rustc_abi::layout::coroutine::variant_entries_of,rustc_abi::layout::coroutine::ineligible_below_of,rustc_abi::layout::coroutine::variant_promoted_of,rustc_abi::layout::coroutine::prefix_wf_of,rustc_abi::layout::coroutine::prefix_fits_bound,rustc_abi::layout::coroutine::assigned_here_of,rustc_abi::layout::coroutine::variant_layout,case_study::iter::Map::yields_entries_of,case_study::counts::filter_count,case_study::counts::filter_yields_below,case_study::counts::filter_selects,case_study::counts::filter_selects_all,case_study::counts::filter_covers_passed,case_study::counts::filter_rejects_rest,case_study::counts::map_count_exact,case_study::counts::map_selected_entries
//@rustc-env: THRUST_SPLIT=1 THRUST_PCSAT_MEMORY=16g
// Generated root: the call graph of `layout()` reaches the functions of row layout in module(s) listed below; see README.md.
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
