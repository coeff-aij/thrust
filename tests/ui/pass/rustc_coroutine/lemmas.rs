//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::lemmas,split,rustc_abi::Size::add_assign,rustc_abi::TargetDataLayout::obj_size_bound,rustc_abi::Size::align_to
// The counting lemmas of thrust/lemmas.rs, which `layout()` (stage 7) and `univariant_biased` use
// and the `layout.rs` root assumes. The code is the module tree under tests/rustc_coroutine/; this
// file selects the lemmas and uses the permutation split as `layout()` does.
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

use case_study::lemmas;
use rustc_index::IndexVec;
use thrust_models::Ghost;

// Of `n` distinct indices, at least `n - b` are at least `b`.
#[thrust_macros::lemma]
#[thrust_macros::requires(b <= n && lemmas::distinct::<u32>(s, n))]
#[thrust_macros::ensures(lemmas::cnt_ge::<u32>(s, n, b) >= n - b)]
fn split(s: Ghost<IndexVec<u32, u32>>, n: usize, b: usize) {
    lemmas::permutation_split(s, n, b);
}
