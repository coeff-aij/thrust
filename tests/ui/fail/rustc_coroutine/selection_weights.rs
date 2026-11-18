//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off --cfg thrust_selection_weights_fail
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::selection_weights::l3_sel_off_by_one
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// The fail twin of selection_weights.rs: `l3_sel` with a sum one too large (`cfg(thrust_selection_weights_fail)`). The code
// is the module tree under tests/rustc_coroutine/.
#![allow(unexpected_cfgs)]
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
