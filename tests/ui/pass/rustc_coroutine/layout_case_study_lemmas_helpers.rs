//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::lemmas::l3,case_study::lemmas::absent,case_study::lemmas::l4_all,case_study::lemmas::l4,case_study::lemmas::l0,case_study::lemmas::l5,case_study::lemmas::l6,case_study::lemmas::permutation_split,case_study::lemmas::permutation_split_le,case_study::lemmas::distinct_of_injective,case_study::lemmas::all_below,case_study::lemmas::below_at_least,case_study::lemmas::occurs,case_study::lemmas::index_occurs,case_study::lemmas::every_index_occurs
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
