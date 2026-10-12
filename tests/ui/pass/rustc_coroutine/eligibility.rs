//@ignore-on-host: the query needs more memory and time than a ui run gives (see README.md)
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::coroutine::coroutine_saved_local_eligibility
// Stage 5 of the rustc-coroutine verification target: `coroutine_saved_local_eligibility` of
// rustc_abi's layout/coroutine.rs.
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
