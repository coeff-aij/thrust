//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::counts::acc_l3,case_study::counts::acc_absent,case_study::counts::acc_l4_all,case_study::counts::acc_zero,case_study::counts::acc_l0,case_study::counts::acc_l5,case_study::counts::acc_all,case_study::counts::acc_bound,case_study::counts::selects_step,case_study::counts::map_bound,case_study::counts::selects_base,case_study::counts::filter_selects,case_study::counts::selection_of_intro,case_study::counts::map_selected_entries,case_study::counts::selects_count,case_study::counts::selects_all_step,case_study::counts::map_exact,case_study::counts::filter_covers_passed,case_study::counts::filter_rejects_rest,case_study::counts::filter_selects_all,case_study::counts::map_count_exact,case_study::counts::filter_count,case_study::counts::filter_yields_below
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
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
