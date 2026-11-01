//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::lemmas,split,l6_off_by_one
// The counting lemmas of thrust/lemmas.rs, which `layout()` (stage 7) uses and the `layout.rs`
// root assumes. The code is the module tree under tests/rustc_coroutine/; this file selects the
// lemmas and uses the permutation split as `layout()` does.
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

// The fail twin: L6 of thrust/lemmas.rs with its proof (the induction on `k`) unchanged and its
// statement one too large, false at `k == 0`. The `split` client above passes in the same selection,
// so the root is Unsat only because the lemma proofs are checked.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(lemmas::cnt_lt::<u32>(s, k, b) + lemmas::cnt_ge::<u32>(s, k, b) == k + 1)]
fn l6_off_by_one(s: Ghost<IndexVec<u32, u32>>, k: usize, b: usize) {
    if k > 0 {
        l6_off_by_one(s, k - 1, b);
    }
}
