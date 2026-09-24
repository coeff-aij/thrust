//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// Extracted from tests/ui/pass/traits/rustc-coroutine.rs (rustc's
// rustc_index::vec, adapted). Stage 2 of the rustc_coroutine plan (README.md).
// `Idx` and its `usize` impl are copied from idx.rs (stage 2/4) rather than
// re-derived, the same way eligibility.rs reuses bitset.rs.
//
// This is the half of stage 2 that does not need a generic slice. `IndexVec`
// takes the model of the `Vec` it wraps -- the `(array, length)` pair -- and
// its methods carry that model as trusted contracts, per the stage plan
// ("IndexSlice/IndexVec are trusted specs first"). What is checked here is the
// caller: `filled` below is verified against those contracts, and it is the
// shape `coroutine_saved_local_eligibility` builds its `assignments` vector
// with.
//
// `IndexSlice` -- whose `raw: [T]` is a bare slice at a generic element type --
// and the `Index`/`IntoSliceIdx` element access built on it are not here; see
// README.md for where they stand.

use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

use thrust_models::forall;
use thrust_models::model::Int;

// //== ./../rustc_index/src/idx.rs

#[thrust_macros::context]
pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    #[thrust_macros::predicate]
    fn can_new(idx: Int) -> bool;

    #[thrust_macros::predicate]
    fn index_is(self, i: Int) -> bool;

    #[thrust_macros::requires(Self::can_new(idx))]
    #[thrust_macros::ensures(Self::index_is(result, idx))]
    fn new(idx: usize) -> Self;

    #[thrust_macros::ensures(Self::index_is(self, result))]
    fn index(self) -> usize;
}

#[thrust_macros::context]
impl Idx for usize {
    #[thrust_macros::predicate]
    fn can_new(idx: Int) -> bool {
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn index_is(self, i: Int) -> bool {
        // self == i
        "(= self_ i)";
        true
    }

    #[inline]
    fn new(idx: usize) -> Self {
        idx
    }
    #[inline]
    fn index(self) -> usize {
        self
    }
}

// //== ./../rustc_index/src/vec.rs

// `PartialEq, Eq` commented out: the derived `eq` compares the `PhantomData`
// field, whose model is the unit sort, and Thrust panics with
// `unbound var $0` (src/chc/clause_builder.rs:113) -- the same reason
// bitset.rs drops them from `DenseBitSet`.
#[derive(/* PartialEq, Eq, */ Hash)]
#[repr(transparent)]
pub struct IndexVec<I: Idx, T> {
    pub raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

impl<I: Idx, T: thrust_models::Model> thrust_models::Model for IndexVec<I, T> {
    type Ty = <Vec<T> as thrust_models::Model>::Ty;
}

#[thrust_macros::context]
impl<I: Idx, T> IndexVec<I, T> {
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.len() == 0)]
    pub const fn new() -> Self {
        IndexVec::from_raw(Vec::new())
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == raw)]
    pub const fn from_raw(raw: Vec<T>) -> Self {
        IndexVec {
            raw,
            _marker: PhantomData,
        }
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.len() == n)]
    #[thrust_macros::ensures(forall(|k: Int| !(0 <= k && k < n) || result[k] == elem))]
    pub fn from_elem_n(elem: T, n: usize) -> Self
    where
        T: Clone,
    {
        IndexVec::from_raw(vec![elem; n])
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == (*self).len())]
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures((result == true) == ((*self).len() == 0))]
    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(<I as Idx>::can_new((*self).len()))]
    #[thrust_macros::ensures(<I as Idx>::index_is(result, (*self).len()))]
    pub fn next_index(&self) -> I {
        I::new(self.raw.len())
    }

    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(<I as Idx>::can_new((*self).len()))]
    #[thrust_macros::ensures(!self == (*self).push(d))]
    #[thrust_macros::ensures(<I as Idx>::index_is(result, (*self).len()))]
    pub fn push(&mut self, d: T) -> I {
        let idx = self.next_index();
        self.raw.push(d);
        idx
    }

    // rustc reaches the elements through `Index<R: IntoSliceIdx<I, [T]>>` on
    // `IndexSlice`; that path is the part of stage 2 that waits on generic
    // slices, so the element read is spelled out on `IndexVec` here.
    #[inline]
    #[thrust::trusted]
    #[thrust_macros::requires(forall(|i: Int| !<I as Idx>::index_is(index, i) || (0 <= i && i < (*self).len())))]
    #[thrust_macros::ensures(forall(|i: Int| !<I as Idx>::index_is(index, i) || *result == (*self)[i]))]
    pub fn at(&self, index: I) -> &T {
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
#[thrust_macros::ensures(forall(|k: Int| !(0 <= k && k < n) || result[k] == elem))]
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
                    && forall(|k: Int| !(0 <= k && k < i) || v[k] == elem.at_entry())
        );
        // Every entry is one more than the element asked for, so `filled` no
        // longer returns `n` copies of `elem`.
        v.push(elem + 1);
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
