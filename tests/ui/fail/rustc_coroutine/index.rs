//@compile-flags: -Adead_code -C debug-assertions=off
//@no-rustfix
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 THRUST_TRY_SPECS=1
//@rustc-env: THRUST_VERIFY_ONLY=rustc_index::**,crate
//@rustc-env: THRUST_SPLIT=1 THRUST_SPLIT_GOALS=1
// Stages 2 to 4 of the rustc-coroutine verification target: rustc_index (`Idx`, `IndexVec` and
// `IndexSlice`, the bit sets, and the own iterators of rewrites.md R2 to R4), and the test code of
// this file (`crate`): `filled`, `two_members` and `column_bound`, the callers the trusted
// contracts are checked against (rewrites.md S5).
// The code is the module tree under tests/rustc_coroutine/; this file selects the stages and
// drives them.
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

use thrust_models::forall;

use case_study::USize;
use rustc_index::bit_set::{BitMatrix, DenseBitSet, WordIter};
use rustc_index::{Idx, IdxRange, IndexVec};

#[thrust_macros::context]
impl<I: Idx, T> IndexVec<I, T> {
    // rustc reaches the elements through `Index<R: IntoSliceIdx<I, [T]>>` on
    // `IndexSlice`; that path is the part of stage 2 that waits on generic
    // slices, so the element read is spelled out on `IndexVec` here.
    #[inline]
    // Trusted: the body's `Vec<T>` at a type parameter is typed as the (array, length) pair, not the sequence the contract reads.
    #[thrust::trusted]
    #[thrust_macros::requires(forall(|i: USize| <I as Idx>::index_is(index, i) ==> (0 <= i && i < (*self).len())))]
    #[thrust_macros::ensures(forall(|i: USize| <I as Idx>::index_is(index, i) ==> *result == (*self)[i]))]
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
#[thrust_macros::ensures(forall(|k: USize| 0 <= k && k < n ==> result[k] == elem))]
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
                    && forall(|k: USize| 0 <= k && k < i ==> v[k] == elem.at_entry())
        );
        v.push(elem);
        i += 1;
    }
    v
}

// `<[T]>::fill`, at the word type, for `insert_all`.
#[thrust::extern_spec_fn]
#[thrust_macros::ensures((!slice).len() == (*slice).len())]
#[thrust_macros::ensures(forall(|k: USize| 0 <= k && k < (*slice).len() ==> (!slice)[k] == value))]
fn _extern_spec_slice_fill_word(slice: &mut [u64], value: u64) {
    <[u64]>::fill(slice, value)
}

// The count of members, through `insert`'s contract: inserting 1 twice counts once.
#[thrust_macros::ensures(DenseBitSet::<usize>::card(result) == 2)]
fn two_members() -> DenseBitSet<usize> {
    let mut set: DenseBitSet<usize> = DenseBitSet::new_empty(5);
    set.insert(1);
    set.insert(1);
    set.insert(2);
    set
}

// Every column a row of a matrix yields is below its column bound, given that no bit is set at
// or past it.
#[thrust_macros::requires(BitMatrix::<usize, usize>::wf(*m) && 0 < (*m).num_rows && *(*m).col_bound == 5
    && BitMatrix::<usize, usize>::cols_below(*m, *(*m).col_bound))]
#[thrust_macros::ensures(true)]
fn column_bound(m: &BitMatrix<usize, usize>) {
    let mut it = m.iter(0);
    match it.next() {
        Some(e) => assert!(e < 5),
        None => {}
    }
}

fn main() { //~ ERROR: Unsat
    drive_iterators();
    drive_index_vec();
    drive_bit_sets();
}

fn drive_iterators() {
    let mut range: IdxRange<usize> = IdxRange::new(0, 3);
    // Verified via `IdxRange::new`'s own ensures.
    assert!(range.start == 0 && range.end == 3);
    // Verified via the `next` contract above: `Idx for usize` reads
    // `index_is(self, i)` as `self == i`, so the k-th call yields `Some(k)`.
    let a = range.next();
    // Broken narrowly: `IdxRange::next`'s contract pins this to `Some(0)`.
    assert!(a.unwrap() == 1);
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

fn drive_index_vec() {
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

fn drive_bit_sets() {
    let mut set: DenseBitSet<usize> = DenseBitSet::new_empty(5);
    set.insert(3);
    assert!(set.contains(3));
    assert!(!set.contains(2));

    // `iter`'s ensures make the iterator's elements the set's members, so the only element is 3;
    // `IteratorSpec` carries the domain bound to the second call.
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
