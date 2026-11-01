//@ignore-on-host: draft, as the pass root (README.md)
//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=case_study::counts,map_bound_unordered
// The count of a variant's fields of thrust/counts.rs, which `layout()`'s per-variant closure
// (stage 7) uses and the `layout.rs` root assumes. The code is the module tree under
// tests/rustc_coroutine/; this file selects the lemmas.
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

use case_study::counts;
use rustc_index::IndexVec;
use thrust_models::model::{Array, Int};
use thrust_models::forall;

// The fail twin: `map_bound` of thrust/counts.rs with its induction on `k` and its statement, but
// without the premise that the map is increasing, so that a map may send two positions to one
// entry (m = 2, k = 1).
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(forall(|m: Int, f: Array<Int, Int>|
    !(0 <= m
        && forall(|j: Int| !(0 <= j && j < m)
            || (0 <= f[j] && f[j] < k && (*a)[<u32 as rustc_index::Idx>::index_logic((*fields)[f[j]])] == *e)))
    || m <= counts::acc_cnt::<u32, u32, u32, u32>(*fields, *a, *e, k)))]
fn map_bound_unordered(fields: &IndexVec<u32, u32>, a: &IndexVec<u32, u32>, e: &u32, k: usize) {
    if k > 0 {
        map_bound_unordered(fields, a, e, k - 1);
    }
}
