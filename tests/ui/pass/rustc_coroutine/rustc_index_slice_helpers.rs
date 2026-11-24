//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_index::slice::IndexSlice::len,rustc_index::slice::IndexSlice::next_index,rustc_index::slice::IndexSlice::iter,rustc_index::slice::IndexSlice::iter_enumerated,rustc_index::slice::IndexSlice::indices,rustc_index::slice::IndexSlice::iter_mut,rustc_index::slice::IndexSlice::invert_bijective_mapping,rustc_index::slice::IndexSlice::index,rustc_index::slice::IndexSlice::index_mut
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Generated root: the call graph of `layout()` reaches the functions of row rustc_index in module(s) listed below; see README.md.
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
