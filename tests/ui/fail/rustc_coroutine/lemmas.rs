//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::lemmas,split,l6_off_by_one,occurs_one_more
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
use rustc_index::{Idx, IndexVec};
use thrust_models::model::Int;
use thrust_models::{exists, forall, Ghost};

// Of `n` distinct indices, at least `n - b` are at least `b`.
#[thrust_macros::lemma]
#[thrust_macros::requires(b <= n && lemmas::distinct::<u32>(s, n))]
#[thrust_macros::ensures(lemmas::cnt_ge::<u32>(s, n, b) >= n - b)]
fn split(s: Ghost<IndexVec<u32, u32>>, n: usize, b: usize) {
    lemmas::permutation_split(s, n, b);
}

// The fail twins, each a lemma of thrust/lemmas.rs with its proof unchanged and its statement
// false: L6 (the induction on `k`) one too large, false at `k == 0`, and `every_index_occurs`
// below. The `split` client above passes in the same selection, so the root is Unsat only because
// the lemma proofs are checked.
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(lemmas::cnt_lt::<u32>(s, k, b) + lemmas::cnt_ge::<u32>(s, k, b) == k + 1)]
fn l6_off_by_one(s: Ghost<IndexVec<u32, u32>>, k: usize, b: usize) {
    if k > 0 {
        l6_off_by_one(s, k - 1, b);
    }
}

// `every_index_occurs` reaching one index further, false at `m == n`, as every index is below `n`.
#[thrust_macros::lemma]
#[thrust_macros::variant(m)]
#[thrust_macros::requires(
    m <= n
        && lemmas::distinct::<u32>(s, n)
        && forall(|j: Int| !(0 <= j && j < n) || <u32 as Idx>::index_logic(s[j]) < n)
)]
#[thrust_macros::ensures(
    forall(|i: Int| !(0 <= i && i <= m) || exists(|j: Int| 0 <= j && j < n && <u32 as Idx>::index_logic(s[j]) == i))
)]
fn occurs_one_more(s: Ghost<IndexVec<u32, u32>>, n: usize, m: usize) {
    if m > 0 {
        occurs_one_more(s, n, m - 1);
        lemmas::index_occurs(s, n, m - 1);
    }
}
