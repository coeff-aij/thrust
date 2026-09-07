//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// Extracted from tests/ui/pass/traits/rustc-coroutine.rs (rustc's
// rustc_index::idx, adapted). Only attributes, `Model` impls and the
// predicate definitions below are added; bodies and signatures are verbatim.

use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

// //== ./../rustc_index/src/idx.rs

#[thrust_macros::context]
pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    #[thrust_macros::predicate]
    fn can_new(idx: thrust_models::model::Int) -> bool;

    #[thrust_macros::predicate]
    fn index_is(self, i: thrust_models::model::Int) -> bool;

    #[thrust_macros::requires(Self::can_new(idx))]
    #[thrust_macros::ensures(Self::index_is(result, idx))]
    fn new(idx: usize) -> Self;

    #[thrust_macros::ensures(Self::index_is(self, result))]
    fn index(self) -> usize;

    #[inline]
    #[thrust_macros::requires(
        thrust_models::forall(|i: thrust_models::model::Int|
            Self::index_is(*self, i) ==> Self::can_new(i + amount)
        )
    )]
    fn increment_by(&mut self, amount: usize) {
        *self = self.plus(amount);
    }

    #[inline]
    #[must_use = "Use `increment_by` if you wanted to update the index in-place"]
    #[thrust_macros::requires(
        thrust_models::forall(|i: thrust_models::model::Int|
            Self::index_is(self, i) ==> Self::can_new(i + amount)
        )
    )]
    fn plus(self, amount: usize) -> Self {
        Self::new(self.index() + amount)
    }
}

#[thrust_macros::context]
impl Idx for usize {
    #[thrust_macros::predicate]
    fn can_new(idx: thrust_models::model::Int) -> bool {
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn index_is(self, i: thrust_models::model::Int) -> bool {
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

// The body uses `as` casts, which Thrust does not support: marked trusted.
#[thrust_macros::context]
impl Idx for u32 {
    #[thrust_macros::predicate]
    fn can_new(idx: thrust_models::model::Int) -> bool {
        // idx <= u32::MAX as usize
        "(<= idx 4294967295)";
        true
    }

    #[thrust_macros::predicate]
    fn index_is(self, i: thrust_models::model::Int) -> bool {
        // self == i
        "(= self_ i)";
        true
    }

    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }
    #[inline]
    #[thrust::trusted]
    #[thrust::callable]
    fn index(self) -> usize {
        self as usize
    }
}

/// Own iterator standing in for `(start..end).map(I::new)`: yields
/// `I::new(start)`, `I::new(start + 1)`, ..., `I::new(end - 1)`.
// `Clone` commented out (/* Debug-style */ marker, see CLAUDE.md/agent brief):
// deriving it on this generic struct panics Thrust with `unbound var $0` in
// src/chc/clause_builder.rs:113 as soon as any requires/ensures on
// `IdxRange<I>` references `Self::Item` (repro: derive `Clone` on a generic
// struct `S<I>`, give it a local shadow `Iterator` impl with `type Item = I`
// and any predicate mentioning `Option<Self::Item>` or `forall(|x| ...)`
// over it -- the same construct without the `Clone` derive verifies fine).
// tests/ui/pass/rustc_coroutine/bitset.rs already hit and commented out the
// same derive on its own copy of IdxRange for the same reason.
// #[derive(Clone)]
pub struct IdxRange<I: Idx> {
    start: usize,
    end: usize,
    marker: PhantomData<I>,
}

impl<I: Idx> thrust_models::Model for IdxRange<I> {
    type Ty = Self;
}

#[thrust_macros::context]
impl<I: Idx> IdxRange<I> {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.start == start && result.end == end)]
    fn new(start: usize, end: usize) -> IdxRange<I> {
        IdxRange {
            start,
            end,
            marker: PhantomData,
        }
    }
}

// `next()` is left unspecified here (see the report): the real
// `std::iter::Iterator` cannot carry requires/ensures at all (it is defined
// outside this crate, and Thrust rejects requires/ensures attached only to
// an impl method when the trait declaration itself has none -- E0407 "method
// `_thrust_requires_next` is not a member of trait `Iterator`" -- so any
// spec has to live on the trait declaration, shared by every implementor).
// A local shadow trait (matching the technique in
// tests/ui/pass/traits/{take,fuse,id}.rs and
// tests/ui/pass/iterators/annot_range_{next,loop}.rs, each of which keeps
// its own private copy of `trait Iterator` for the same reason) does let a
// spec be declared, using the invariant/completed/step predicate
// abstraction those tests use. That was tried here with `Item = I` (this
// impl's own generic parameter) and a requires of
// `self.start < self.end ==> I::can_new(self.start)`: the file compiles
// and produces no ICE, but the generic verification of `next`'s own body
// (checked once, abstractly over `I: Idx`, independently of any call site)
// comes back Unsat even with `main` empty and even with every predicate
// body replaced by a trivial `"true"`. Reducing further shows the call
// `I::new(n)` inside the body needs `I::can_new(n)`, and the solver ends up
// with two distinct declared symbols for it --
// `q_can_new_<hash><a0>` (from `IdxRange<I>`'s own generic parameter `I`)
// and `q_can_new_<hash><a1>` (from `Idx::new`'s own generic `Self`, called
// here as `I::new`) -- that are never unified, so the fact assumed via the
// first can never discharge the obligation stated in terms of the second.
// This looks like a genuine gap in connecting an enclosing impl's generic
// parameter to a differently-scoped generic `Self` at a call site, distinct
// from (and found on top of) the E0407 restriction; not re-investigated
// further here per the time box. `IdxRange`'s own copy in
// tests/ui/pass/rustc_coroutine/bitset.rs hits the same wall and also
// leaves `next` unspecified (there via `#[thrust::trusted] #[thrust::callable]`).
mod idx_range_iter {
    use super::{Idx, IdxRange};

    #[thrust_macros::context]
    pub(super) trait Iterator {
        type Item;
        fn next(&mut self) -> Option<Self::Item>;
    }

    #[thrust_macros::context]
    impl<I: Idx> Iterator for IdxRange<I> {
        type Item = I;

        // Body left `trusted`: proving the internal call `I::new(n)`
        // satisfies its own `Idx::can_new` precondition hits the gap
        // described above.
        #[thrust::trusted]
        #[thrust::callable]
        fn next(&mut self) -> Option<I> {
            if self.start < self.end {
                let n = self.start;
                self.start += 1;
                Some(I::new(n))
            } else {
                None
            }
        }
    }
}
use idx_range_iter::Iterator as _;

type Word = u64;

/// Own iterator standing in for `slice::Iter<'a, Word>` (whose raw pointer
/// fields have no model in Thrust): yields `&words[0]`, ..., `&words[len - 1]`.
pub struct WordIter<'a> {
    words: &'a [Word],
    pos: usize,
}

impl<'a> thrust_models::Model for WordIter<'a> {
    type Ty = Self;
}

#[thrust_macros::context]
impl<'a> WordIter<'a> {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.pos == 0)]
    fn new(words: &'a [Word]) -> WordIter<'a> {
        WordIter { words, pos: 0 }
    }
}

// Same E0407 restriction as `IdxRange` above: the real `std::iter::Iterator`
// cannot carry requires/ensures, so any spec has to go through a local
// shadow trait declaring it once for every implementor. Attempting the
// invariant/completed/step abstraction here (mirroring `IdxRange`'s
// attempt) additionally hits `error[E0277]: can't compare`
// `<&'a u64 as thrust_models::Model>::Ty` `with` `<&'a u64 as
// thrust_models::Model>::Ty`, `` `PartialEq` `not implemented`'' at the
// `#[thrust_macros::predicate]` expansion for `step`/the trait's `next`,
// even with an explicit `where <&'a Word as thrust_models::Model>::Ty:
// PartialEq` bound on the impl (std.rs's blanket `impl<'a, T: ?Sized> Model
// for &'a T` gives `Ty = &'a <T as Model>::Ty`, and `model::Int`'s own
// `PartialEq` impl -- `impl<T> PartialEq<T> for Int where T: Model<Ty =
// Self>` -- does not appear to satisfy what the reference blanket
// `PartialEq` impl needs here). `Option<&'a Word>` equality (needed for
// `result == Some(i)` in the shared `next` ensures) is therefore left
// unexpressed, matching `IdxRange` above; `next` is left unspecified with a
// bare shadow-trait signature and a `#[thrust::trusted] #[thrust::callable]`
// body.
mod word_iter_iter {
    use super::{Word, WordIter};

    #[thrust_macros::context]
    pub(super) trait Iterator {
        type Item;
        fn next(&mut self) -> Option<Self::Item>;
    }

    #[thrust_macros::context]
    impl<'a> Iterator for WordIter<'a> {
        type Item = &'a Word;

        #[thrust::trusted]
        #[thrust::callable]
        fn next(&mut self) -> Option<&'a Word> {
            if self.pos < self.words.len() {
                let item = &self.words[self.pos];
                self.pos += 1;
                Some(item)
            } else {
                None
            }
        }
    }
}
use word_iter_iter::Iterator as _;

fn main() {
    let mut range: IdxRange<usize> = IdxRange::new(0, 3);
    // Verified via `IdxRange::new`'s own ensures.
    assert!(range.start == 1 && range.end == 3);
    // `next()`'s return value carries no verified relationship to the
    // input (see the comment above), so it isn't asserted on here; the
    // calls below only exercise that Thrust accepts the (trusted) code.
    let _a = range.next();
    let _b = range.next();
    let _c = range.next();
    let _d = range.next();

    let mut wi: WordIter<'static> = WordIter::new(words());
    // Verified via `WordIter::new`'s own ensures.
    assert!(wi.pos == 0);
    // Same caveat as `IdxRange::next` above: exercised only structurally.
    let _w0 = wi.next();
    let _w1 = wi.next();
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length == 3
        && (*result).array[0] == 10
        && (*result).array[1] == 20
        && (*result).array[2] == 30
)]
fn words() -> &'static [Word] {
    unimplemented!()
}
