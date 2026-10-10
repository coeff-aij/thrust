//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
// Stage 3 of the rustc-coroutine verification target: rustc_index's bit sets.
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
#![feature(custom_inner_attributes)]
#![feature(new_range_api)]
#![thrust::verify_only("rustc_index::bit_set", "two_members", "column_bound")]

#[path = "../../../rustc_coroutine/compiler/rustc_hashes/src/lib.rs"]
pub mod rustc_hashes;
#[path = "../../../rustc_coroutine/compiler/rustc_index/src/lib.rs"]
pub mod rustc_index;
#[path = "../../../rustc_coroutine/compiler/rustc_abi/src/lib.rs"]
pub mod rustc_abi;
#[path = "../../../rustc_coroutine/thrust/mod.rs"]
pub mod case_study;

use thrust_models::forall;

use case_study::USize;
use case_study::iter::Iterator;
use rustc_index::bit_set::{BitMatrix, DenseBitSet};

// `vec![elem; n]` expands to `std::vec::from_elem`; specified at the word type of
// bit_set.rs. It stays in this root: Thrust applies it to every instantiation of `from_elem`.
#[thrust::extern_spec_fn]
#[thrust_macros::ensures(result.len() == n)]
#[thrust_macros::ensures(forall(|k: USize| k < n ==> result[k] == elem))]
fn _extern_spec_vec_from_elem_word(elem: u64, n: usize) -> Vec<u64> {
    std::vec::from_elem(elem, n)
}


// The count of members, through `insert`'s contract: inserting 1 twice counts once.
#[thrust_macros::ensures(result.3 == 2)]
fn two_members() -> DenseBitSet<usize> {
    let mut set: DenseBitSet<usize> = DenseBitSet::new_empty(5);
    set.insert(1);
    set.insert(1);
    set.insert(2);
    set
}

// Every column a row of a matrix yields is below its column bound, whatever the bits.
#[thrust_macros::requires(BitMatrix::<usize, usize>::wf(*m) && 0 < (*m).num_rows && *(*m).col_bound == 5)]
#[thrust_macros::ensures(true)]
fn column_bound(m: &BitMatrix<usize, usize>) {
    let mut it = m.iter(0);
    match it.next() {
        Some(e) => assert!(e < 5),
        None => {}
    }
}

fn main() {
    let mut set: DenseBitSet<usize> = DenseBitSet::new_empty(5);
    set.insert(3);
    assert!(set.contains(3));
    assert!(!set.contains(2));

    // `iter`'s ensures make the iterator's elements the set's members, so the only element is 3;
    // the iterator trait carries the domain bound to the second call.
    let mut it = set.iter();
    match it.next() {
        Some(e) => assert!(e == 3),
        None => {}
    }
    match it.next() {
        Some(e) => assert!(e < 5),
        None => {}
    }
}
