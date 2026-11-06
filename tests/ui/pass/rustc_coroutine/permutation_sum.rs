//@ignore-on-host: draft, the inductions of `sum_occurring_step` and `sum_at_occurring` get no answer (see README.md)
//@check-pass
//@edition: 2024
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_abi::layout::sum_occurring_step,rustc_abi::layout::sum_at_occurring,rustc_abi::layout::sum_occurring_le,rustc_abi::layout::sum_at_le,rustc_abi::Size::add_assign,rustc_abi::Size::bits,rustc_abi::Size::align_to
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// The permutation sum of layout.rs, which bounds the weight of the fields `univariant_biased`'s
// field loop has placed, in memory order, by the weight of all the fields: `sum_at_le` and the
// lemmas its induction uses, over the counting functions of thrust/lemmas.rs.
// The code is the module tree under tests/rustc_coroutine/; this file selects the lemmas.
// Each goal is solved with the clauses it depends on (`THRUST_SPLIT_GOALS`).
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
