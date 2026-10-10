//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Stage 2 of the rustc-coroutine verification target: rustc_index's `IndexVec` and `IndexSlice`.
// `filled` is the caller the trusted `IndexVec` contracts are checked against (rewrites.md S5).
// The code is the module tree under tests/rustc_coroutine/; this file selects the stage and
// drives it.
#![feature(custom_inner_attributes)]
#![feature(new_range_api)]
#![thrust::verify_only("rustc_index::vec", "rustc_index::slice", "filled")]

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
use rustc_index::{Idx, IndexVec};

#[thrust_macros::context]
impl<I: Idx, T> IndexVec<I, T> {
    // rustc reaches the elements through `Index<R: IntoSliceIdx<I, [T]>>` on
    // `IndexSlice`; that path is the part of stage 2 that waits on generic
    // slices, so the element read is spelled out on `IndexVec` here.
    #[inline]
    // Trusted: the body's `Vec<T>` at a type parameter is typed as the (array, length) pair, not the sequence the contract reads.
    #[thrust::trusted]
    #[thrust_macros::requires(forall(|i: USize| !<I as Idx>::index_is(index, i) || (0 <= i && i < (*self).len())))]
    #[thrust_macros::ensures(forall(|i: USize| !<I as Idx>::index_is(index, i) || *result == (*self)[i]))]
    fn at(&self, index: I) -> &T {
        &self.raw[index.index()]
    }
}

// //== stage 2 property
//
// Filling a fresh `IndexVec` one `push` at a time leaves exactly one entry per
// step and every entry is the element that was pushed -- what
// `coroutine_saved_local_eligibility` needs of its `assignments` vector, and
// what its `IndexVec::from_elem_n(Unassigned, nb_locals)` stands for.

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result.len() == n)]
#[thrust_macros::ensures(forall(|k: USize| !(0 <= k && k < n) || result[k] == elem))]
#[thrust_macros::context]
fn filled(n: usize, elem: i64) -> IndexVec<usize, i64> {
    let mut v: IndexVec<usize, i64> = IndexVec::new();
    let mut i = 0;
    while i < n {
        thrust_macros::invariant!(
            |v: IndexVec<usize, i64>,
             i: usize,
             n: thrust_models::FnParam<usize>,
             elem: thrust_models::FnParam<i64>|
                v.len() == i
                    && i <= n.at_entry()
                    && forall(|k: USize| !(0 <= k && k < i) || v[k] == elem.at_entry())
        );
        v.push(elem);
        i += 1;
    }
    v
}

fn main() {
    let mut v: IndexVec<usize, i64> = IndexVec::new();
    let a = v.push(10);
    let b = v.push(20);
    assert!(v.len() == 2);
    assert!(*v.at(a) == 10);
    assert!(*v.at(b) == 20);

    let w = filled(3, 7);
    assert!(w.len() == 3);
    assert!(*w.at(2) == 7);
}
