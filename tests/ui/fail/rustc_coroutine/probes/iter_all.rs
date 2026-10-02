//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens -A unused_imports
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1

use std::marker::PhantomData;
use thrust_models::model::{Closure, Int, Mut, Seq, UInt};
use thrust_models::{exists, forall, Ghost};

// The iterator trait, local to the case study (rewrites.md R9): Creusot's `common.rs` as the
// Creusot benchmark cases of the fork declare it (tests/ui/pass/creusot/range.rs), with the
// predicates `produces`, `completed` and `invariant` (`true` unless the impl says otherwise), the
// laws `produces_refl` and `produces_trans`, which every impl inherits and Thrust checks at each
// impl, and `next` with Creusot's contract. It shadows std's `Iterator`.
#[thrust_macros::context]
trait Iterator
where
    Self: thrust_models::Model,
    Self::Item: thrust_models::Model,
{
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::invariant(*a))]
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self) {}

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    fn next(&mut self) -> Option<Self::Item>;
}

pub struct DenseBitSet {
    words: Vec<u64>,
}

impl thrust_models::Model for DenseBitSet {
    type Ty = UInt;
}

pub struct BitIter {
    word: u64,
}

impl thrust_models::Model for BitIter {
    type Ty = UInt;
}

#[thrust_macros::context]
impl DenseBitSet {
    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::ensures(result == *self)]
    fn iter(&self) -> BitIter {
        BitIter { word: 0 }
    }
}

#[thrust_macros::context]
impl Iterator for BitIter {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        self.next_bit()
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        o + visited.len() == self
            && forall(|i: Int| !(0 <= i && i < visited.len()) || 0 <= visited[i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == 0 && *self == !self
    }
}

// The trusted stub behind `next`: Thrust trusts a function only on its own contract, and the
// method of an impl of the local trait has the trait's.
#[thrust_macros::context]
impl BitIter {
    #[thrust::trusted]
    #[thrust_macros::requires(<Self as Iterator>::invariant(*self))]
    #[thrust_macros::ensures(
        <Self as Iterator>::invariant(!self)
            && (result == None ==> <Self as Iterator>::completed(self))
            && forall(|x: <usize as thrust_models::Model>::Ty| result == Some(x) ==> <Self as Iterator>::produces(*self, Seq::singleton(x), !self))
    )]
    fn next_bit(&mut self) -> Option<usize> {
        None
    }
}
// Rewrite (rewrites.md R8): `iter_all(it, f)` for `it.all(f)`, with a verified body. Like `all`
// it stops at the first item the closure rejects. `F: Fn` as in `Filter`, the closure's
// precondition must hold on every item the iterator can yield, and the items are `Copy` (the
// site iterates references), so the loop can record what it passed to the closure.
struct IterAllSpec<I, F>(PhantomData<(I, F)>);

#[thrust_macros::context]
impl<I, F> IterAllSpec<I, F>
where
    I: Iterator,
    F: Fn(I::Item) -> bool,
    I::Item: thrust_models::Model + Copy,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn pre_all(iter: I, func: F) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, s.push(e), i) || thrust_macros::pre!(func(e)))))
    }

    // `b` follows `a` by yielding `x`.
    #[thrust_macros::predicate]
    fn stepped(a: I, x: I::Item, b: I, func: F) -> bool {
        Self::pre_all(a, func) && I::produces(a, Seq::singleton(x), b)
    }

    // `pre_all` moves along one yielded item; the lemma is proved apart from the loop.
    #[thrust_macros::requires(Self::stepped(a, x, b, func))]
    #[thrust_macros::ensures(Self::pre_all(b, func))]
    fn pre_all_step(a: Ghost<I>, x: Ghost<I::Item>, b: Ghost<I>, func: Ghost<F>) {}

    #[thrust_macros::predicate]
    fn accepted(func: F, seen: Vec<I::Item>) -> bool {
        forall(|k: Int| !(0 <= k && k < seen.len()) || thrust_macros::post!(func(seen[k]), true))
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter) && IterAllSpec::<I, F>::pre_all(iter, f))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<I::Item as thrust_models::Model>::Ty>,
           mid: <I as thrust_models::Model>::Ty|
        I::produces(iter, visited, mid)
            && (result == true ==>
                exists(|fin: <I as thrust_models::Model>::Ty| I::completed(Mut::new(mid, fin)))
                    && forall(|k: Int| !(0 <= k && k < visited.len()) || thrust_macros::post!(f(visited[k]), true)))
            && (result == false ==>
                0 < visited.len()
                    && thrust_macros::post!(f(visited[visited.len() - 1]), false)
                    && forall(|k: Int| !(0 <= k && k < visited.len() - 1) || thrust_macros::post!(f(visited[k]), true))))
)]
fn iter_all<I, F>(iter: I, f: F) -> bool
where
    I: Iterator,
    F: Fn(I::Item) -> bool,
    I::Item: thrust_models::Model + Copy,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    I::produces_refl(&it);
    // `seen` records the items passed to the closure, for the loop invariant.
    let mut seen: Vec<I::Item> = Vec::new();
    loop {
        thrust_macros::invariant!(
            |it: I, seen: Vec<I::Item>, iter: thrust_models::FnParam<I>, f: F|
                I::invariant(it)
                    && I::produces(iter.at_entry(), seen, it)
                    && IterAllSpec::<I, F>::accepted(f, seen)
                    && IterAllSpec::<I, F>::pre_all(it, f)
        );
        let before = thrust_macros::ghost!(|it: I| -> I { it });
        let Some(x) = it.next() else {
            return true;
        };
        let yielded = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
        let after = thrust_macros::ghost!(|it: I| -> I { it });
        let fs = thrust_macros::ghost!(|f: F| -> F { f });
        IterAllSpec::<I, F>::pre_all_step(before, yielded, after, fs);
        if !f(x) {
            return false;
        }
        seen.push(x);
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn small(set: &DenseBitSet) -> bool {
    iter_all(set.iter(), thrust_macros::closure!(requires(i < 100), ensures(true), |i: usize| -> bool { i < 100 }))
}

fn main() {}
