//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest THRUST_SOLVER_TIMEOUT_SECS=120

// Extracted from tests/ui/pass/traits/rustc-coroutine.rs (rustc's
// rustc_index::idx, adapted). Only attributes, `Model` impls and the
// predicate definitions below are added; bodies and signatures are verbatim.

use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

use thrust_models::exists;
use thrust_models::forall;
use thrust_models::model::Int;

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
// deriving it on this generic struct panics Thrust with `unbound var $0`
// (src/chc/clause_builder.rs:113) while analysing
// `<IdxRange<I> as Clone>::clone`, on the inner
// `<PhantomData<I> as Clone>::clone` call whose std spec is
// `{ () | true /\ nu = *$0 }` with `generic_args=[PhantomData<I/#0>]` -- i.e.
// the unit-modelled `&PhantomData<I>` argument. Re-checked after moving
// `next`'s spec onto the `extern_spec_fn` wrapper below: the ICE is
// independent of that (it needs no requires/ensures mentioning `Self::Item`
// at all, just the derive). `bitset.rs`'s own copy of `IdxRange` and its
// `DenseBitSet`/`BitMatrix` comment out the same derives for the same reason.
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

// `next` implements the real `std::iter::Iterator`, so its spec cannot be
// written as attributes on the impl method itself: `requires`/`ensures`
// expand into companion items placed next to the method, and in an
// `impl Trait for Ty` every item must be a trait member
// (`error[E0407]: method `_thrust_requires_next` is not a member of trait
// `Iterator``). The spec therefore lives on a sibling *inherent* impl, as an
// `#[thrust::extern_spec_fn]` wrapper whose body tail-calls the impl method.
// Thrust resolves the wrapper's target through `Instance::try_resolve`,
// registers the contract under the impl method's `DefId`, checks the impl
// body against it and uses it at static call sites; see
// tests/ui/pass/rustc_coroutine/notes/foreign_trait_impl_specs.md. Written
// this way, the `I::can_new(n)` obligation inside the body *is* discharged
// from the wrapper's `requires` -- the two-forall-sorts mismatch reported for
// the earlier local-shadow-trait attempt does not occur here (dropping the
// `requires` clause below turns the file `Unsat`, so the body is really
// checked against this contract).
impl<I: Idx> Iterator for IdxRange<I> {
    type Item = I;

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

#[thrust_macros::context]
impl<I: Idx> IdxRange<I> {
    // `Idx::can_new` / `Idx::index_is` take `Int`, but `IdxRange`'s model is
    // the struct itself, so `(*it).start` keeps its Rust type `usize` in a
    // formula and cannot be passed to them (`error[E0308]: expected `Int`,
    // found `usize``). The `s == (*it).start` guard under `forall` -- `Int`
    // on the left, where `impl<T: Model<Ty = Int>> PartialEq<T> for Int`
    // applies -- is what bridges the two.
    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(
        forall(|s: Int| s == (*it).start && s < (*it).end ==> <I as Idx>::can_new(s))
    )]
    #[thrust_macros::ensures(
        forall(|s: Int| s == (*it).start && s < (*it).end
            ==> exists(|x: <I as thrust_models::Model>::Ty|
                    result == Some(x) && <I as Idx>::index_is(x, s))
                && s + 1 == (!it).start
                && (!it).end == (*it).end)
    )]
    #[thrust_macros::ensures(
        !((*it).start < (*it).end)
            ==> result == None && (!it).start == (*it).start && (!it).end == (*it).end
    )]
    fn _extern_spec_next(it: &mut IdxRange<I>) -> Option<I>
    where
        I: thrust_models::Model,
        <I as thrust_models::Model>::Ty: PartialEq,
    {
        <IdxRange<I> as Iterator>::next(it)
    }
}

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

// The `words` field has the slice type `&'a [Word]`, and `WordIter`'s model
// is the struct itself, so in a `requires`/`ensures` -- which is compiled as
// an ordinary Rust function -- the field keeps that Rust type: the `Seq`
// accessors are rejected (`error[E0609]: no field `length` on type `[u64]``,
// likewise `array`) and `.len()` reaches
// `not implemented: unsupported method call in formula: ... len#0`
// (src/analyze/annot_fn.rs:915; only the `Seq`/`Array` model methods are
// handled there). The three predicates below are therefore the only way to
// name `words`' length and elements; a predicate body must be a raw SMT-LIB2
// string literal, so they project the model tuple
// `(words: (array, length), pos)` by hand.
#[thrust_macros::context]
impl<'a> WordIter<'a> {
    /// `self.words.length == n`.
    #[thrust_macros::predicate]
    fn words_len_is(self, n: Int) -> bool {
        "(= n (tuple_proj<Array<Int-Int>-Int>.1
                  (tuple_proj<Tuple<Array<Int-Int>-Int>-Int>.0 self_)))";
        true
    }

    /// `self.words.array[i] == w`.
    #[thrust_macros::predicate]
    fn word_is(self, i: Int, w: Int) -> bool {
        "(= w (select (tuple_proj<Array<Int-Int>-Int>.0
                          (tuple_proj<Tuple<Array<Int-Int>-Int>-Int>.0 self_))
                      i))";
        true
    }

    /// `dist.words == self.words`.
    #[thrust_macros::predicate]
    fn same_words(self, dist: Self) -> bool {
        "(= (tuple_proj<Tuple<Array<Int-Int>-Int>-Int>.0 dist)
            (tuple_proj<Tuple<Array<Int-Int>-Int>-Int>.0 self_))";
        true
    }

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.pos == 0)]
    #[thrust_macros::ensures(Self::words_len_is(result, (*words).length))]
    #[thrust_macros::ensures(forall(|i: Int| Self::word_is(result, i, (*words).array[i])))]
    fn new(words: &'a [Word]) -> WordIter<'a> {
        WordIter { words, pos: 0 }
    }
}

// Same `extern_spec_fn` idiom as `IdxRange::next` above. `Option<&'a Word>`
// models as `Option<&'a Int>`, so the yielded word has to be named by
// `exists(|x: Int| result == Some(&x) && ..)`: writing the closure parameter
// at the Rust element type instead gives
// `error[E0308]: mismatched types ... expected `&Int`, found `&u64``
// (`Option`'s `PartialEq` needs both sides at the same model type). No
// `<&u64 as Model>::Ty` `PartialEq` bound is needed with this shape.
impl<'a> Iterator for WordIter<'a> {
    type Item = &'a Word;

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

#[thrust_macros::context]
impl<'a> WordIter<'a> {
    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::same_words(*it, !it))]
    #[thrust_macros::ensures(forall(|n: Int, p: Int|
        Self::words_len_is(*it, n) && p == (*it).pos
            ==> (p < n ==> exists(|x: Int| result == Some(&x) && Self::word_is(*it, p, x))
                    && p + 1 == (!it).pos)
                && (n <= p ==> result == None && (!it).pos == (*it).pos)))]
    fn _extern_spec_next(it: &mut WordIter<'a>) -> Option<&'a Word> {
        <WordIter<'a> as Iterator>::next(it)
    }
}

fn main() {
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
    (*result).length == 3
        && (*result).array[0] == 10
        && (*result).array[1] == 20
        && (*result).array[2] == 30
)]
fn words() -> &'static [Word] {
    unimplemented!()
}
