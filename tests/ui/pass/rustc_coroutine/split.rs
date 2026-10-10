//@ignore-on-host: not yet verifiable, PCSat fails on a forall function inside a define-fun-rec: a crash in RecFunGraph.encode by default, a wrong unsat with rec_fun_graph_unknowns off (fptprove thrust-benchmarks unsolved/rec_fun_forall_fun_2026-10-11/)
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
// Part of stage 7 of the rustc-coroutine verification target: `split_memory_order`, the loop of
// `layout()` that splits univariant's memory order, and the counting lemmas it applies
// (`case_study::lemmas`). The code is the module tree under tests/rustc_coroutine/; this file
// selects the functions and drives them.
#![feature(custom_inner_attributes)]
#![feature(new_range_api)]
#![thrust::verify_only("rustc_abi::layout::coroutine::split_memory_order", "case_study::lemmas")]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

fn main() {}
