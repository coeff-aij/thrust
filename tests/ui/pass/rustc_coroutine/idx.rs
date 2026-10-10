//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Stages 2 and 4 of the rustc-coroutine verification target: rustc_index's `Idx` and the own
// iterators of rewrites.md R2 to R4 (`IdxRange`, `WordIter`, `SliceIter`, `IterEnumerated`).
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
#![feature(custom_inner_attributes)]
#![feature(new_range_api)]
#![thrust::verify_only("rustc_index::idx", "rustc_index::bit_set::WordIter", "rustc_index::slice::SliceIter", "rustc_index::slice::IterEnumerated")]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use rustc_index::IdxRange;
use rustc_index::bit_set::WordIter;

fn main() {
    let mut range: IdxRange<usize> = IdxRange::new(0, 3);
    // Verified via `IdxRange::new`'s own ensures.
    assert!(range.start == 0 && range.end == 3);
    // Verified via the `next` contract above: `Idx for usize` reads
    // `index_is(self, i)` as `self == i`, so the k-th call yields `Some(k)`.
    let a = range.next();
    assert!(a.unwrap() == 0);
    assert!(range.start == 1);
    let b = range.next();
    assert!(b.unwrap() == 1);
    let c = range.next();
    assert!(c.unwrap() == 2);
    assert!(range.start == 3);
    let d = range.next();
    assert!(d.is_none());

    let mut wi: WordIter<'static> = WordIter::new(words());
    // Verified via `WordIter::new`'s own ensures.
    assert!(wi.pos == 0);
    // Verified via the `next` contract above.
    let w0 = wi.next();
    assert!(*w0.unwrap() == 10);
    assert!(wi.pos == 1);
    let w1 = wi.next();
    assert!(*w1.unwrap() == 20);
    assert!(wi.pos == 2);
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).len() == 3
        && (*result)[0] == 10
        && (*result)[1] == 20
        && (*result)[2] == 30
)]
fn words() -> &'static [u64] {
    unimplemented!()
}
