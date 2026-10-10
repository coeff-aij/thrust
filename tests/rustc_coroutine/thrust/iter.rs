//! The case study's iterator adapters and consumers for those std.rs does not specify
//! (rewrites.md R8), over std's `Iterator` and std.rs's `IteratorSpec`, and `SliceIter`'s `find`.

use crate::thrust_models;
use std::marker::PhantomData;

use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{Ghost, exists, forall};

use crate::IteratorSpec;
use crate::rustc_index::{Idx, IndexVec, SliceIter};
use crate::case_study::USize;

#[thrust_macros::context]
impl<'a, T: thrust_models::Model> SliceIter<'a, T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::ensures(result.0 == raw && result.1 == 0)]
    pub fn new(raw: &'a [T]) -> SliceIter<'a, T> {
        SliceIter { raw, pos: 0 }
    }

    // `Iterator::find` over this iterator: the items in order until the closure accepts one. `P:
    // Fn` in place of std's `FnMut` (the closures at the call sites capture by shared reference),
    // so the postcondition names the closure's answers: it rejected every item before the one
    // found, or every item. The iterator ends right after the item found, or at the end.
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*self))]
    #[thrust_macros::requires(forall(|x: <&'a T as thrust_models::Model>::Ty| thrust_macros::pre!(predicate(&x))))]
    #[thrust_macros::ensures((!self).0 == (*self).0 && (*self).1 <= (!self).1 && (!self).1 <= (*self).0.len())]
    #[thrust_macros::ensures(result == None ==> (!self).1 == (*self).0.len())]
    #[thrust_macros::ensures(forall(|x: <&'a T as thrust_models::Model>::Ty| result == Some(x)
        ==> (*self).1 < (!self).1
            && x == &(*self).0[(!self).1 - 1]
            && thrust_macros::post!(predicate(&x), true)))]
    #[thrust_macros::ensures(result == None ==> forall(|k: Int|
        !((*self).1 <= k && k < (!self).1) || thrust_macros::post!(predicate(&&(*self).0[k]), false)))]
    #[thrust_macros::ensures(result == None || forall(|k: Int|
        !((*self).1 <= k && k + 1 < (!self).1) || thrust_macros::post!(predicate(&&(*self).0[k]), false)))]
    pub fn find<P: Fn(&&'a T) -> bool>(&mut self, predicate: P) -> Option<&'a T> {
        let this = self;
        while let Some(x) = this.next() {
            thrust_macros::invariant!(
                |this: &mut SliceIter<'a, T>, self: thrust_models::FnParam<&mut SliceIter<'a, T>>, predicate: P|
                    !this == !self.at_entry()
                        && (*this).0 == (*self.at_entry()).0
                        && (*self.at_entry()).1 <= (*this).1
                        && (*this).1 <= (*this).0.len()
                        && forall(|x: <&'a T as thrust_models::Model>::Ty| thrust_macros::pre!(predicate(&x)))
                        && forall(|k: Int| !((*self.at_entry()).1 <= k && k < (*this).1)
                            || thrust_macros::post!(predicate(&&(*this).0[k]), false))
            );
            if predicate(&x) {
                return Some(x);
            }
        }
        None
    }
}

// Rewrite (rewrites.md R8): a local `Map` in place of `iter::Map`, evaluation 1's adapter
// (tests/ui/pass/creusot/map.rs), implementing std's `Iterator` and std.rs's `IteratorSpec`. The model is the inner iterator and
// the closure state; `produces` carries the input items `s` and the chain `fs` of closure states.
pub struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I: thrust_models::Model, F> thrust_models::Model for Map<I, F> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<F>);
}

// Creusot's `next_precondition`, `preservation_inv`, `reinitialize` and `produces`, and the lemma
// that proves `produces_trans`.
#[thrust_macros::context]
impl<I, B, F> Map<I, F>
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::requires(
        I::inv(iter)
            && Self::reinitialize()
            && Self::preservation_inv(iter, func)
            && Self::next_precondition(iter, func)
    )]
    #[thrust_macros::ensures(result.0 == iter && result.1 == func)]
    pub fn new(iter: I, func: F) -> Map<I, F> {
        Map { iter, func }
    }

    #[thrust_macros::predicate]
    fn next_precondition(iter: I, func: F) -> bool {
        forall(|e: <I::Item as thrust_models::Model>::Ty| forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, Seq::singleton(e), i) || thrust_macros::pre!(func(e))))
    }

    #[thrust_macros::predicate]
    fn preservation_inv(iter: I, func: F) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e1: <I::Item as thrust_models::Model>::Ty|
        forall(|e2: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
        forall(|f1: Closure<F>|
        forall(|f2: Closure<F>|
        forall(|b: <B as thrust_models::Model>::Ty|
            !(thrust_macros::hist_inv!(func, f1)
                && I::produces(iter, s.push(e1).push(e2), i)
                && thrust_macros::pre!(f1(e1))
                && thrust_macros::post!(Mut::new(f1, f2)(e1), b))
                || thrust_macros::pre!(f2(e2)))))))))
    }

    #[thrust_macros::predicate]
    fn reinitialize() -> bool {
        forall(|cur: <I as thrust_models::Model>::Ty| forall(|fin: <I as thrust_models::Model>::Ty| forall(|f: Closure<F>|
            !I::completed(Mut::new(cur, fin))
                || (Self::next_precondition(fin, f)
                    && Self::preservation_inv(fin, f)))))
    }

    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Vec<B>, o: Self, s: Seq<<I::Item as thrust_models::Model>::Ty>, fs: Seq<F>) -> bool {
        thrust_macros::hist_inv!(s0.1, o.1)
            && s.len() == visited.len()
            && I::produces(s0.0, s, o.0)
            && fs.len() == visited.len() + 1
            && fs[0] == s0.1
            && fs[visited.len()] == o.1
            && forall(|k: USize|
                !(0 <= k && k < visited.len())
                    || (thrust_macros::hist_inv!(s0.1, fs[k])
                        && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k]), visited[k])))
    }

    // `produces_at` of the joined witnesses: the input items concatenated and the closure states
    // joined at their shared state.
    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
            || Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc)))))))]
    fn produces_trans_at(
        a: Ghost<Self>,
        ab: Ghost<Seq<<B as thrust_models::Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<B as thrust_models::Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }
}

#[thrust_macros::context]
impl<I, B, F> Iterator for Map<I, F>
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    type Item = B;

    fn next(&mut self) -> Option<B> {
        let pre = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
        let r = self.iter.next();
        match r {
            Some(v) => {
                let e = thrust_macros::ghost!(|v: <I as Iterator>::Item| -> <I as Iterator>::Item { v });
                let b = (self.func)(v);
                let post = thrust_macros::ghost!(|self: &mut Self| -> Self { *self });
                let bm = thrust_macros::ghost!(|b: B| -> B { b });
                // Keeps `self` live at the snapshot `post`.
                let _keep = &*self;
                Some(b)
            }
            None => None,
        }
    }
}

#[thrust_macros::context]
impl<I, B, F> IteratorSpec for Map<I, F>
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        Self::reinitialize()
            && Self::preservation_inv(self.0, self.1)
            && I::inv(self.0)
            && Self::next_precondition(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool {
        thrust_macros::hist_inv!(self.1, o.1)
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|fs: Seq<Closure<F>>|
                Self::produces_at(self, visited, o, s, fs)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
        let ga = thrust_macros::ghost!(|a: &Self| -> Self { *a });
        let gb = thrust_macros::ghost!(|b: &Self| -> Self { *b });
        let gc = thrust_macros::ghost!(|c: &Self| -> Self { *c });
        let gab = thrust_macros::ghost!(|ab: Seq<<B as thrust_models::Model>::Ty>| -> Seq<<B as thrust_models::Model>::Ty> { ab });
        let gbc = thrust_macros::ghost!(|bc: Seq<<B as thrust_models::Model>::Ty>| -> Seq<<B as thrust_models::Model>::Ty> { bc });
        Self::produces_trans_at(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
    }

    fn produces_refl(a: &Self) {}
}

// Rewrite (rewrites.md R8): a local `Filter` in place of `iter::Filter`, in the form of `Map`
// above, with two of the three restrictions of Creusot's `Filter` (creusot-std/src/std/iter/
// filter.rs): the closure's captures are used immutably (`P: Fn`, so its state never changes),
// and, in place of a closure without a precondition, the precondition holds on every item the
// inner iterator can yield (`pre_all`; rustc's closure in `layout()` can panic). The closure's
// postcondition need not be precise: `produces` states the count only, the items yielded are at
// most the input items the inner iterator produced, and not which of them.
pub struct Filter<I, P> {
    iter: I,
    predicate: P,
}

impl<I: thrust_models::Model, P> thrust_models::Model for Filter<I, P> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<P>);
}

#[thrust_macros::context]
impl<I, P> Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::requires(
        I::inv(iter)
            && Self::reinitialize()
            && Self::pre_all(iter, predicate)
    )]
    #[thrust_macros::ensures(result.0 == iter && result.1 == predicate)]
    pub fn new(iter: I, predicate: P) -> Filter<I, P> {
        Filter { iter, predicate }
    }

    // The closure's precondition holds on every item `iter` can yield, after any number of others.
    #[thrust_macros::predicate]
    fn pre_all(iter: I, func: P) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, s.push(e), i) || thrust_macros::pre!(func(&e)))))
    }

    // Creusot's `reinitialize`: after completion, the precondition holds again.
    #[thrust_macros::predicate]
    fn reinitialize() -> bool {
        forall(|cur: <I as thrust_models::Model>::Ty| forall(|fin: <I as thrust_models::Model>::Ty|
            !I::completed(Mut::new(cur, fin))
                || forall(|f: Closure<P>| Self::pre_all(fin, f))))
    }

    // The precondition holds of `Self`'s state.
    #[thrust_macros::predicate]
    fn pre_ok(a: Self) -> bool {
        Self::pre_all(a.0, a.1)
    }

    // `b` follows `a` by yielding `x`, and the closure is the same.
    #[thrust_macros::predicate]
    fn stepped(a: Self, x: I::Item, b: Self) -> bool {
        Self::pre_ok(a) && I::produces(a.0, Seq::singleton(x), b.0) && a.1 == b.1
    }

    // `pre_all` moves along one yielded item; the lemma proves it apart from the loop that uses it.
    #[thrust_macros::requires(Self::stepped(a, x, b))]
    #[thrust_macros::ensures(Self::pre_ok(b))]
    fn pre_all_step(a: Ghost<Self>, x: Ghost<I::Item>, b: Ghost<Self>) {}

    // `produces` with its input items `s` given.
    #[thrust_macros::predicate]
    fn produces_at(s0: Self, visited: Vec<I::Item>, o: Self, s: Seq<<I::Item as thrust_models::Model>::Ty>) -> bool {
        s0.1 == o.1
            && I::produces(s0.0, s, o.0)
            && visited.len() <= s.len()
    }

    // `produces_at` of the joined witnesses.
    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        !(Self::produces_at(a, ab, b, sab) && Self::produces_at(b, bc, c, sbc))
            || Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc)))))]
    fn produces_trans_at(
        a: Ghost<Self>,
        ab: Ghost<Seq<<I::Item as thrust_models::Model>::Ty>>,
        b: Ghost<Self>,
        bc: Ghost<Seq<<I::Item as thrust_models::Model>::Ty>>,
        c: Ghost<Self>,
    ) {
    }
}

#[thrust_macros::context]
impl<I, P> Iterator for Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        // `skipped` records the items the closure rejected, for the loop invariant.
        let this = self;
        let mut skipped: Vec<I::Item> = Vec::new();
        loop {
            thrust_macros::invariant!(
                |this: &mut Filter<I, P>, skipped: Vec<I::Item>, self: thrust_models::FnParam<&mut Filter<I, P>>|
                    !this == !self.at_entry()
                        && Filter::<I, P>::reinitialize()
                        && Filter::<I, P>::pre_all((*this).0, (*this).1)
                        && I::inv((*this).0)
                        && (*this).1 == (*self.at_entry()).1
                        && I::produces((*self.at_entry()).0, skipped, (*this).0)
            );
            let before = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
            let Some(x) = this.iter.next() else {
                break;
            };
            let yielded = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
            let after = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
            Filter::<I, P>::pre_all_step(before, yielded, after);
            if (this.predicate)(&x) {
                return Some(x);
            }
            skipped.push(x);
        }
        None
    }
}

#[thrust_macros::context]
impl<I, P> IteratorSpec for Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{



    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        Self::reinitialize()
            && I::inv(self.0)
            && Self::pre_all(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool {
        exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
            Self::produces_at(self, visited, o, s))
    }

    // The inner iterator produced the rest, then completed.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 == (!self).1
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|mid: <I as thrust_models::Model>::Ty|
                I::produces((*self).0, s, mid)
                    && I::completed(Mut::new(mid, (!self).0))))
    }

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
        let ga = thrust_macros::ghost!(|a: &Self| -> Self { *a });
        let gb = thrust_macros::ghost!(|b: &Self| -> Self { *b });
        let gc = thrust_macros::ghost!(|c: &Self| -> Self { *c });
        let gab = thrust_macros::ghost!(|ab: Seq<<I::Item as thrust_models::Model>::Ty>| -> Seq<<I::Item as thrust_models::Model>::Ty> { ab });
        let gbc = thrust_macros::ghost!(|bc: Seq<<I::Item as thrust_models::Model>::Ty>| -> Seq<<I::Item as thrust_models::Model>::Ty> { bc });
        Self::produces_trans_at(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
    }

    fn produces_refl(a: &Self) {}
}

// Rewrite (rewrites.md R8): `iter_all(it, f)` for `it.all(f)`, with a verified body. Like `all`
// it stops at the first item the closure rejects. `F: Fn` as in `Filter`, the closure's
// precondition must hold on every item the iterator can yield, and the items are `Copy` (the
// site iterates references), so the loop can record what it passed to the closure.
pub struct IterAllSpec<I, F>(PhantomData<(I, F)>);

#[thrust_macros::context]
impl<I, F> IterAllSpec<I, F>
where
    I: IteratorSpec,
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
        forall(|k: USize| !(0 <= k && k < seen.len()) || thrust_macros::post!(func(seen[k]), true))
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(iter) && IterAllSpec::<I, F>::pre_all(iter, f))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<I::Item as thrust_models::Model>::Ty>,
           mid: <I as thrust_models::Model>::Ty|
        I::produces(iter, visited, mid)
            && (result == true ==>
                exists(|fin: <I as thrust_models::Model>::Ty| I::completed(Mut::new(mid, fin)))
                    && forall(|k: USize| !(0 <= k && k < visited.len()) || thrust_macros::post!(f(visited[k]), true)))
            && (result == false ==>
                0 < visited.len()
                    && thrust_macros::post!(f(visited[visited.len() - 1]), false)
                    && forall(|k: USize| !(0 <= k && k < visited.len() - 1) || thrust_macros::post!(f(visited[k]), true))))
)]
pub fn iter_all<I, F>(iter: I, f: F) -> bool
where
    I: IteratorSpec,
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
                I::inv(it)
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

// Rewrite (rewrites.md R8): `extend` with a verified body, in place of `Extend::extend` (whose
// std body is not analysed): `self` ends as its entry value followed by what `iter` produced
// before it completed.
#[thrust_macros::context]
impl<I: Idx, T: thrust_models::Model + Copy> IndexVec<I, T>
where
    I: thrust_models::Model,
    I::Ty: PartialEq,
    T::Ty: PartialEq,
{
    #[thrust_macros::requires(J::inv(iter))]
    #[thrust_macros::ensures(
        exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
               mid: <J as thrust_models::Model>::Ty,
               fin: <J as thrust_models::Model>::Ty|
            J::produces(iter, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && !self == (*self).concat(visited))
    )]
    pub fn extend_from<J>(&mut self, iter: J)
    where
        J: IteratorSpec + Iterator<Item = T>,
        <J as thrust_models::Model>::Ty: PartialEq,
    {
        let this = self;
        let mut it = iter;
        J::produces_refl(&it);
        // `pushed` records what `it` produced, so the invariant needs no existential sequence.
        let mut pushed: Vec<T> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: J, this: &mut IndexVec<I, T>, pushed: Vec<T>, iter: thrust_models::FnParam<J>, self: thrust_models::FnParam<&mut IndexVec<I, T>>|
                    !this == !self.at_entry()
                        && J::inv(it)
                        && J::produces(iter.at_entry(), pushed, it)
                        && *this == (*self.at_entry()).concat(pushed)
            );
            this.raw.push(x);
            pushed.push(x);
        }
    }
}

// Rewrite (rewrites.md R8): `collect` with a verified body, in place of `Iterator::collect` into
// an `IndexVec`: the collection is what the iterator produced before it completed.
#[thrust_macros::context]
#[thrust_macros::requires(J::inv(iter))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
           mid: <J as thrust_models::Model>::Ty,
           fin: <J as thrust_models::Model>::Ty|
        J::produces(iter, visited, mid)
            && J::completed(Mut::new(mid, fin))
            && result == visited)
)]
pub fn collect_index_vec<I, T, J>(iter: J) -> IndexVec<I, T>
where
    I: Idx + thrust_models::Model,
    I::Ty: PartialEq,
    T: thrust_models::Model,
    T::Ty: PartialEq,
    J: IteratorSpec + Iterator<Item = T>,
    <J as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    J::produces_refl(&it);
    let mut v: Vec<T> = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: J, v: Vec<T>, iter: thrust_models::FnParam<J>|
                J::inv(it) && J::produces(iter.at_entry(), v, it)
        );
        v.push(x);
    }
    // `IndexVec::from_raw(v)`, written out: its model is the sequence `v`.
    IndexVec {
        raw: v,
        _marker: PhantomData,
    }
}

// Rewrite (rewrites.md R8): `collect` into a `Result` of an `IndexVec`, in place of the
// `FromIterator for Result<V, E>` of std: the first `Err` item is returned; otherwise the
// collection holds the `Ok` payloads of what the iterator produced before it completed.
#[thrust_macros::context]
#[thrust_macros::requires(J::inv(iter))]
#[thrust_macros::ensures(
    forall(|v: <IndexVec<I, T> as thrust_models::Model>::Ty| result != Ok(v)
        || exists(|visited: Seq<<Result<T, E> as thrust_models::Model>::Ty>,
                   mid: <J as thrust_models::Model>::Ty,
                   fin: <J as thrust_models::Model>::Ty|
            J::produces(iter, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && visited.len() == v.len()
                && forall(|k: USize| !(0 <= k && k < v.len()) || visited[k] == Ok(v[k]))))
)]
pub fn collect_index_vec_result<I, T, E, J>(iter: J) -> Result<IndexVec<I, T>, E>
where
    I: Idx + thrust_models::Model,
    I::Ty: PartialEq,
    T: thrust_models::Model,
    T::Ty: PartialEq,
    E: thrust_models::Model,
    E::Ty: PartialEq,
    J: IteratorSpec + Iterator<Item = Result<T, E>>,
    <J as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    J::produces_refl(&it);
    let mut v: Vec<T> = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: J, v: Vec<T>, iter: thrust_models::FnParam<J>|
                J::inv(it)
                    && exists(|s: Seq<<Result<T, E> as thrust_models::Model>::Ty>|
                        J::produces(iter.at_entry(), s, it)
                            && s.len() == v.len()
                            && forall(|k: USize| !(0 <= k && k < v.len()) || s[k] == Ok(v[k])))
        );
        match x {
            Ok(y) => v.push(y),
            Err(e) => return Err(e),
        }
    }
    Ok(IndexVec {
        raw: v,
        _marker: PhantomData,
    })
}
