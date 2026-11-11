//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::coroutine::layout,rustc_abi::layout::coroutine::bit_iter_yields_below,rustc_abi::layout::coroutine::index_is_only,rustc_abi::layout::coroutine::layouts_wf_of_entries,rustc_abi::layout::coroutine::layout_pre_of_wf,rustc_abi::layout::coroutine::promote_locals,rustc_abi::layout::coroutine::split_prefix_fields,rustc_abi::layout::coroutine::split_in_memory_order,rustc_abi::layout::coroutine::combine_offsets,rustc_abi::layout::coroutine::combine_wf_of,rustc_abi::layout::coroutine::variant_field_layouts,rustc_abi::layout::coroutine::assigned_count_of,rustc_abi::layout::coroutine::variant_layout,rustc_abi::layout::coroutine::variant_env_of,rustc_abi::layout::coroutine::variant_entries_of,rustc_abi::layout::coroutine::variant_promoted_of,rustc_abi::layout::coroutine::ineligible_below_of,rustc_abi::layout::coroutine::prefix_wf_of,rustc_abi::layout::coroutine::prefix_fits_bound,rustc_index::slice::IterEnumerated::yields_last,case_study::iter,case_study::counts::filter_count,case_study::counts::filter_selects,case_study::counts::filter_selects_all,case_study::counts::filter_covers_passed,case_study::counts::filter_rejects_rest,case_study::counts::map_count_exact,case_study::counts::map_selected_entries,case_study::counts::selection_of_intro,case_study::counts::filter_yields_below
//@rustc-env: THRUST_SPLIT=1
// Each goal of the functions marked `#[thrust::split_goals]` is solved with the clauses it depends
// on, the other goals in their classes. The `proof_assert!` of `prefix_fits` in `variant_layout` is
// the goal of the fail twin's part 291 and is killed at the wrapper's 8 GB when the solver runs
// beside other tests, though it answers at 8 GB alone; see the fail twin's header for the query
// handed to fptprove.
// The limit returns to 8 GB with the fail twin's.
//@rustc-env: THRUST_PCSAT_MEMORY=16g
// Stage 7 of the rustc-coroutine verification target: `layout()` of rustc_abi's
// layout/coroutine.rs, with the local iterator adapters it calls (rewrites.md R8). The counting
// lemmas it uses are assumed here: those of thrust/lemmas.rs are verified by the `lemmas.rs`
// root, those of thrust/counts.rs by the `counts.rs` root. The lemmas over the per-variant closure's
// `Map` and `Filter` are selected here, as a closure held inside a struct cannot be handed to a
// callee Thrust does not analyze; three of them assume their `ensures` (fallback, README.md).
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
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
