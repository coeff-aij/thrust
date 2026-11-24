//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_index::vec::IndexVec::new,rustc_index::vec::IndexVec::from_raw,rustc_index::vec::IndexVec::from_elem,rustc_index::vec::IndexVec::from_elem_n,rustc_index::vec::IndexVec::as_slice,rustc_index::vec::IndexVec::as_mut_slice,rustc_index::vec::IndexVec::push,rustc_index::vec::IndexVec::deref,rustc_index::vec::IndexVec::deref_mut,rustc_index::vec::_extern_spec_index_vec_deref,rustc_index::vec::_extern_spec_index_vec_deref_mut,rustc_index::vec::IndexVec::into_iter,rustc_index::vec::{impl}::into_iter
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
