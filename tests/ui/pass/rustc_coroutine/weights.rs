//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::weights
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// The weight lemmas of thrust/weights.rs: a selection of distinct indices below `n` weighs at
// most the first `n` weights. The code is the module tree under tests/rustc_coroutine/; this file
// selects the lemmas. `thrust_weights_fail` is set only by the fail twin. Each goal is solved with the clauses it depends on (`THRUST_SPLIT_GOALS`).
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
