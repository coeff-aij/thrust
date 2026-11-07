//! The case study's iterator adapters and consumers for those std.rs does not specify, or
//! specifies with a precondition the case study's closures do not meet (`max_by_key`)
//! (rewrites.md R8), over std's `Iterator` and std.rs's `IteratorSpec`.
#![allow(unexpected_cfgs)]

use crate::thrust_models;
use std::marker::PhantomData;

use thrust_models::model::{Array, Closure, Int, Mut, Seq};
use thrust_models::{Ghost, exists, forall};

use crate::IteratorSpec;
use crate::rustc_index::{Idx, IndexVec};
use crate::case_study::USize;

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

    // What the map yields is what its closure returned from a state its `hist_inv!` reaches, so a
    // property of every such result holds of every item yielded; here, being an entry of `l`.
    // The caller shows the `requires` from the closure's `ensures`.
    #[thrust_macros::requires(forall(|f1: Closure<F>, f2: Closure<F>, e: <I::Item as thrust_models::Model>::Ty, b: <B as thrust_models::Model>::Ty|
        !(thrust_macros::hist_inv!((*it).1, f1) && thrust_macros::post!(Mut::new(f1, f2)(e), b))
            || exists(|i: USize| 0 <= i && i < (*l).len() && b == (*l)[i])))]
    #[thrust_macros::ensures(forall(|v: Seq<<B as thrust_models::Model>::Ty>, o: <Self as thrust_models::Model>::Ty, k: USize|
        !(<Self as IteratorSpec>::produces(*it, v, o) && 0 <= k && k < v.len())
            || exists(|i: USize| 0 <= i && i < (*l).len() && v[k] == (*l)[i])))]
    #[thrust_macros::lemma]
    pub fn yields_entries_of<L: Idx + thrust_models::Model>(it: &Self, l: &crate::rustc_index::IndexSlice<L, B>) {}

    // `produces_at` of the joined witnesses: the input items concatenated and the closure states
    // joined at their shared state.
    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc) ==> Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc)))))))]
    #[thrust_macros::lemma]
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
// inner iterator can yield (`pre_all`; rustc's closure in `layout()` can panic). Creusot's third,
// a precise closure, is not required: `produces` states the closure's answer on each input item,
// `true` on the items yielded and `false` on the others, the statement Creusot's comment on
// `precise` gives as the alternative; with a precise closure it is Creusot's equivalence.
// `next` also states that the item it returns is the last the inner iterator produced: `produces`
// places it in the inner items at its index map's position, and later items there may be
// rejected ones, so it does not give the last; `univariant_biased`'s `next` calls read that form.
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

    // The closure answers `r` on the `k`-th item of `s`.
    #[thrust_macros::predicate]
    pub(crate) fn answers(func: Closure<P>, s: Seq<<I::Item as thrust_models::Model>::Ty>, k: Int, r: bool) -> bool {
        thrust_macros::post!(func(&s[k]), r)
    }

    // `produces` with the inner iterator's items `s` and Creusot's index map `f` given: the items
    // yielded are those of `s` at the increasing positions `f`, so no more than `s` (stated, as an
    // increasing map gives it only by induction), and the closure answered `true` on the items at
    // those positions and `false` on the others.
    #[thrust_macros::predicate]
    pub(crate) fn produces_at(s0: Self, visited: Vec<I::Item>, o: Self, s: Seq<<I::Item as thrust_models::Model>::Ty>, f: Array<Int, Int>) -> bool {
        s0.1 == o.1
            && I::produces(s0.0, s, o.0)
            && visited.len() <= s.len()
            && forall(|i: Int| !(0 <= i && i < visited.len())
                || (0 <= f[i] && f[i] < s.len() && visited[i] == s[f[i]]))
            && forall(|i: Int, j: Int| !(0 <= i && i < j && j < visited.len()) || f[i] < f[j])
            && forall(|k: Int| !(0 <= k && k < s.len())
                || ((!exists(|j: Int| 0 <= j && j < visited.len() && f[j] == k)
                        || Self::answers(s0.1, s, k, true))
                    && (exists(|j: Int| 0 <= j && j < visited.len() && f[j] == k)
                        || Self::answers(s0.1, s, k, false))))
    }

    // `next`'s step, with the witnesses of `produces` named: the inner items are those the closure
    // rejected followed by `x`, which it accepted, and the index map sends the one item yielded
    // to `x`'s position.
    #[thrust_macros::requires(
        a.1 == b.1
            && I::produces(a.0, skipped, mid.0)
            && I::produces(mid.0, Seq::singleton(x), b.0)
            && forall(|k: Int| !(0 <= k && k < skipped.len()) || Self::answers(a.1, skipped, k, false))
            && forall(|p: Int| !(p == skipped.len())
                || Self::answers(a.1, skipped.concat(Seq::singleton(x)), p, true))
    )]
    #[thrust_macros::ensures(forall(|p: Int| !(p == skipped.len())
        || Self::produces_at(a, Seq::singleton(x), b, skipped.concat(Seq::singleton(x)),
            Array::<Int, Int>::from_fn(|i: Int| p))))]
    #[thrust_macros::lemma]
    fn next_at(
        a: Ghost<Self>,
        skipped: Ghost<Seq<<I::Item as thrust_models::Model>::Ty>>,
        mid: Ghost<Self>,
        x: Ghost<I::Item>,
        b: Ghost<Self>,
    ) {
    }

    // `produces_at` of the joined witnesses: the inner items concatenated and the index maps
    // joined, the second shifted past the first's inner items (Creusot's `Mapping`, here
    // `Array::from_fn`).
    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|fab: Array<Int, Int>| forall(|fbc: Array<Int, Int>|
            !(Self::produces_at(a, ab, b, sab, fab) && Self::produces_at(b, bc, c, sbc, fbc))
                || Self::produces_at(a, ab.concat(bc), c, sab.concat(sbc),
                    Array::<Int, Int>::from_fn(|i: Int| if i < ab.len() { fab[i] } else { fbc[i - ab.len()] + sab.len() })))))))]
    #[thrust_macros::lemma]
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
{
    type Item = I::Item;

    // The trait's contract, and the item returned is the last the inner iterator produced.
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*self))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!self)
            && (result == None ==> <Self as IteratorSpec>::completed(self))
            && forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
                ==> (<Self as IteratorSpec>::produces(*self, Seq::singleton(x), !self)
                    && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
                        I::produces((*self).0, s.push(x), (!self).0))))
    )]
    fn next(&mut self) -> Option<I::Item> {
        // `skipped` records the items the closure rejected, for the loop invariant: the inner
        // iterator yielded them, and the closure answered `false` on each.
        let this = self;
        let entry = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
        let mut skipped: Vec<I::Item> = Vec::new();
        loop {
            thrust_macros::invariant!(
                |this: &mut Filter<I, P>, skipped: Vec<I::Item>, entry: Ghost<Filter<I, P>>, self: thrust_models::FnParam<&mut Filter<I, P>>|
                    !this == !self.at_entry()
                        && entry == *self.at_entry()
                        && Filter::<I, P>::reinitialize()
                        && Filter::<I, P>::pre_all((*this).0, (*this).1)
                        && I::inv((*this).0)
                        && (*this).1 == (*self.at_entry()).1
                        && I::produces((*self.at_entry()).0, skipped, (*this).0)
                        && forall(|k: Int| !(0 <= k && k < skipped.len())
                            || Filter::<I, P>::answers((*this).1, skipped, k, false))
            );
            let before = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
            let Some(x) = this.iter.next() else {
                break;
            };
            let yielded = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
            let after = thrust_macros::ghost!(|this: &mut Filter<I, P>| -> Filter<I, P> { *this });
            Filter::<I, P>::pre_all_step(before, yielded, after);
            let accepted = (this.predicate)(&x);
            // The fail twin of the filter root sets this cfg: `next` then returns the item whether
            // or not the closure accepted it, against the `ensures` that the closure answered
            // `true` on the item returned.
            #[cfg(thrust_filter_fail)]
            let accepted = true;
            if accepted {
                let rejected = thrust_macros::ghost!(|skipped: Vec<I::Item>| -> Seq<<I::Item as thrust_models::Model>::Ty> { skipped });
                Filter::<I, P>::next_at(entry, rejected, before, yielded, after);
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
{



    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        Self::reinitialize()
            && I::inv(self.0)
            && Self::pre_all(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<Self::Item>, o: Self) -> bool {
        exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|f: Array<Int, Int>|
            Self::produces_at(self, visited, o, s, f)))
    }

    // Creusot's `completed`: the inner iterator produced the rest, all of which the closure
    // rejected, then completed.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 == (!self).1
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|mid: <I as thrust_models::Model>::Ty|
                I::produces((*self).0, s, mid)
                    && I::completed(Mut::new(mid, (!self).0))
                    && forall(|k: Int| !(0 <= k && k < s.len()) || Self::answers((*self).1, s, k, false))))
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
                    && forall(|k: USize| 0 <= k && k < visited.len() ==> thrust_macros::post!(f(visited[k]), true)))
            && (result == false ==>
                0 < visited.len()
                    && thrust_macros::post!(f(visited[visited.len() - 1]), false)
                    && forall(|k: USize| 0 <= k && k < visited.len() - 1 ==> thrust_macros::post!(f(visited[k]), true))))
)]
pub fn iter_all<I, F>(iter: I, f: F) -> bool
where
    I: IteratorSpec,
    F: Fn(I::Item) -> bool,
    I::Item: thrust_models::Model + Copy,
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

// Rewrite (rewrites.md R21): `max_by_key(it, f)` for `it.max_by_key(f)`, with a verified body.
// Like core's (`Iterator::max_by_key` through `cmp::max_by`) it keeps the last item of greatest
// key. The closure's precondition need hold only on the items the iterator can yield, where
// std.rs's `max_by_key` requires it of every value; `F: Fn` as in `iter_all`, and the items are
// `Copy`, so the loop can record them with the candidate's position. Creusot (3620de437) specifies
// no `max_by_key`, and Verus (d804d56) only `cmp::max_by_key` of two values
// (vstd/std_specs/cmp.rs:313), not the iterator's. The contract states that the result is one of
// the items produced up to completion, `None` exactly when there is none, and not which of them
// has the greatest key.
pub struct MaxByKeySpec<I, B, F>(PhantomData<(I, B, F)>);

#[thrust_macros::context]
impl<I, B, F> MaxByKeySpec<I, B, F>
where
    I: IteratorSpec,
    F: Fn(&I::Item) -> B,
    B: thrust_models::Model,
    I::Item: thrust_models::Model + Copy,
{
    #[thrust_macros::predicate]
    fn pre_all(iter: I, func: F) -> bool {
        forall(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|e: <I::Item as thrust_models::Model>::Ty|
        forall(|i: <I as thrust_models::Model>::Ty|
            !I::produces(iter, s.push(e), i) || thrust_macros::pre!(func(&e)))))
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
}

#[thrust_macros::context]
#[thrust_macros::requires(I::inv(iter) && MaxByKeySpec::<I, B, F>::pre_all(iter, f))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<I::Item as thrust_models::Model>::Ty>,
           mid: <I as thrust_models::Model>::Ty,
           fin: <I as thrust_models::Model>::Ty|
        I::produces(iter, visited, mid)
            && I::completed(Mut::new(mid, fin))
            && (result == None) == (visited.len() == 0)
            && forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
                ==> exists(|j: Int| 0 <= j && j < visited.len() && x == visited[j])))
)]
pub fn max_by_key<I, B, F>(iter: I, f: F) -> Option<I::Item>
where
    I: IteratorSpec,
    F: Fn(&I::Item) -> B,
    B: Ord + crate::PartialOrdSpec,
    I::Item: thrust_models::Model + Copy,
{
    let mut it = iter;
    I::produces_refl(&it);
    // `seen` records the items passed to the closure and `best_pos` the position of the candidate
    // among them, for the loop invariant; the candidate's key and item are kept apart, so that
    // the invariant states the item without a quantifier.
    let mut seen: Vec<I::Item> = Vec::new();
    let mut best_key: Option<B> = None;
    let mut best_item: Option<I::Item> = None;
    let mut best_pos: usize = 0;
    loop {
        thrust_macros::invariant!(
            |it: I, seen: Vec<I::Item>, best_key: Option<B>, best_item: Option<I::Item>, best_pos: usize, iter: thrust_models::FnParam<I>, f: F|
                I::inv(it)
                    && I::produces(iter.at_entry(), seen, it)
                    && MaxByKeySpec::<I, B, F>::pre_all(it, f)
                    && (best_key == None) == (best_item == None)
                    && (best_item == None) == (seen.len() == 0)
                    && (best_item == None || (best_pos < seen.len() && best_item == Some(seen[best_pos])))
        );
        let before = thrust_macros::ghost!(|it: I| -> I { it });
        let Some(x) = it.next() else {
            thrust_macros::proof_assert!(|best_item: Option<I::Item>, seen: Vec<I::Item>, best_pos: usize|
                best_item == None || (best_pos < seen.len() && best_item == Some(seen[best_pos])));
            return best_item;
        };
        let yielded = thrust_macros::ghost!(|x: I::Item| -> I::Item { x });
        let after = thrust_macros::ghost!(|it: I| -> I { it });
        let fs = thrust_macros::ghost!(|f: F| -> F { f });
        MaxByKeySpec::<I, B, F>::pre_all_step(before, yielded, after, fs);
        let k = f(&x);
        // The candidate's key is compared by reference, so that it stays in place when kept.
        let keep = match &best_key {
            Some(bk) => k < *bk,
            None => false,
        };
        if !keep {
            best_pos = seen.len();
            best_key = Some(k);
            best_item = Some(x);
        }
        seen.push(x);
    }
}

// Rewrite (rewrites.md R8): `extend` with a verified body, in place of `Extend::extend` (whose
// std body is not analysed): `self` ends as its entry value followed by what `it` produced
// before it completed.
#[thrust_macros::context]
impl<I: Idx, T: thrust_models::Model + Copy> IndexVec<I, T>
where
    I: thrust_models::Model,
{
    #[thrust_macros::requires(J::inv(it))]
    #[thrust_macros::ensures(
        exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
               mid: <J as thrust_models::Model>::Ty,
               fin: <J as thrust_models::Model>::Ty|
            J::produces(it, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && !self == (*self).concat(visited))
    )]
    pub fn extend_from<J>(&mut self, it: J)
    where
        J: IteratorSpec + Iterator<Item = T>,
    {
        let this = self;
        for x in it {
            thrust_macros::invariant!(
                |iter: J, iter_old: Ghost<J>, it: thrust_models::FnParam<J>, produced: Ghost<Seq<<T as thrust_models::Model>::Ty>>, this: &mut IndexVec<I, T>, self: thrust_models::FnParam<&mut IndexVec<I, T>>|
                    iter_old == it.at_entry()
                        && !this == !self.at_entry()
                        && *this == (*self.at_entry()).concat(produced)
            );
            this.raw.push(x);
        }
    }
}

// Rewrite (rewrites.md R8): `collect` with a verified body, in place of `Iterator::collect` into
// an `IndexVec`: the collection is what the iterator produced before it completed.
#[thrust_macros::context]
#[thrust_macros::requires(J::inv(it))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
           mid: <J as thrust_models::Model>::Ty,
           fin: <J as thrust_models::Model>::Ty|
        J::produces(it, visited, mid)
            && J::completed(Mut::new(mid, fin))
            && result == visited)
)]
pub fn collect_index_vec<I, T, J>(it: J) -> IndexVec<I, T>
where
    I: Idx + thrust_models::Model,
    T: thrust_models::Model,
    J: IteratorSpec + Iterator<Item = T>,
{
    let mut v: Vec<T> = Vec::new();
    for x in it {
        thrust_macros::invariant!(
            |iter: J, iter_old: Ghost<J>, it: thrust_models::FnParam<J>, produced: Ghost<Seq<<T as thrust_models::Model>::Ty>>, v: Vec<T>|
                iter_old == it.at_entry() && v == produced
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
#[thrust_macros::requires(J::inv(it))]
#[thrust_macros::ensures(
    forall(|v: <IndexVec<I, T> as thrust_models::Model>::Ty| result != Ok(v)
        || exists(|visited: Seq<<Result<T, E> as thrust_models::Model>::Ty>,
                   mid: <J as thrust_models::Model>::Ty,
                   fin: <J as thrust_models::Model>::Ty|
            J::produces(it, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && visited.len() == v.len()
                && forall(|k: USize| 0 <= k && k < v.len() ==> visited[k] == Ok(v[k]))))
)]
pub fn collect_index_vec_result<I, T, E, J>(it: J) -> Result<IndexVec<I, T>, E>
where
    I: Idx + thrust_models::Model,
    T: thrust_models::Model,
    E: thrust_models::Model,
    J: IteratorSpec + Iterator<Item = Result<T, E>>,
{
    let mut v: Vec<T> = Vec::new();
    for x in it {
        thrust_macros::invariant!(
            |iter: J, iter_old: Ghost<J>, it: thrust_models::FnParam<J>, produced: Ghost<Seq<<Result<T, E> as thrust_models::Model>::Ty>>, v: Vec<T>|
                iter_old == it.at_entry()
                    && produced.len() == v.len()
                    && forall(|k: USize| 0 <= k && k < v.len() ==> produced[k] == Ok(v[k]))
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

// Fallback: `collect_index_vec` with its `requires` (the iterator's `inv`) assumed,
// for a `collect` of `layout()`'s whose precondition the solver does not answer. The iterator's
// type names closures, so an `assume!` at the call cannot state it; here it is the type
// parameter. The `ensures` is `collect_index_vec`'s.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
           mid: <J as thrust_models::Model>::Ty,
           fin: <J as thrust_models::Model>::Ty|
        J::produces(it, visited, mid)
            && J::completed(Mut::new(mid, fin))
            && result == visited)
)]
pub fn collect_index_vec_assumed<I, T, J>(it: J) -> IndexVec<I, T>
where
    I: Idx + thrust_models::Model,
    T: thrust_models::Model,
    J: IteratorSpec + Iterator<Item = T>,
{
    thrust_macros::assume!(|it: J| J::inv(it));
    collect_index_vec(it)
}

// Fallback: `collect_index_vec_result` with its `requires` assumed, as
// `collect_index_vec_assumed` is for `collect_index_vec`. The `ensures` is
// `collect_index_vec_result`'s.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    forall(|v: <IndexVec<I, T> as thrust_models::Model>::Ty| result != Ok(v)
        || exists(|visited: Seq<<Result<T, E> as thrust_models::Model>::Ty>,
                   mid: <J as thrust_models::Model>::Ty,
                   fin: <J as thrust_models::Model>::Ty|
            J::produces(it, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && visited.len() == v.len()
                && forall(|k: USize| 0 <= k && k < v.len() ==> visited[k] == Ok(v[k]))))
)]
pub fn collect_index_vec_result_assumed<I, T, E, J>(it: J) -> Result<IndexVec<I, T>, E>
where
    I: Idx + thrust_models::Model,
    T: thrust_models::Model,
    E: thrust_models::Model,
    J: IteratorSpec + Iterator<Item = Result<T, E>>,
{
    thrust_macros::assume!(|it: J| J::inv(it));
    collect_index_vec_result(it)
}
