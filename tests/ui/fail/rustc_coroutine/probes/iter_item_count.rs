//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 THRUST_TRY_SPECS=1

use thrust_models::model::{Closure, Int, Mut, Seq};
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
    type Ty = Int;
}

pub struct BitIter {
    word: u64,
}

impl thrust_models::Model for BitIter {
    type Ty = Int;
}

#[thrust_macros::context]
impl DenseBitSet {
    #[thrust::trusted]
    #[thrust::callable]
    #[thrust_macros::ensures(result == *self && 0 <= *self)]
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
        0 <= self
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        0 <= o && o + visited.len() == self
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
// Rewrite (rewrites.md R8): a local `Map` in place of `iter::Map`, evaluation 1's adapter
// (tests/ui/pass/creusot/map.rs) on the local `Iterator`. The model is the inner iterator and
// the closure state; `produces` carries the input items `s` and the chain `fs` of closure states.
struct Map<I, F> {
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
    I: Iterator,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::requires(
        I::invariant(iter)
            && Self::reinitialize()
            && Self::preservation_inv(iter, func)
            && Self::next_precondition(iter, func)
    )]
    #[thrust_macros::ensures(result.0 == iter && result.1 == func)]
    fn new(iter: I, func: F) -> Map<I, F> {
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
            !(thrust_macros::unnest!(func, f1)
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
        thrust_macros::unnest!(s0.1, o.1)
            && s.len() == visited.len()
            && I::produces(s0.0, s, o.0)
            && fs.len() == visited.len() + 1
            && fs[0] == s0.1
            && fs[visited.len()] == o.1
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || (thrust_macros::unnest!(s0.1, fs[k])
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
    I: Iterator,
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

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::reinitialize()
            && Self::preservation_inv(self.0, self.1)
            && I::invariant(self.0)
            && Self::next_precondition(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
        thrust_macros::unnest!(self.1, o.1)
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
}

// Rewrite (rewrites.md R8): a local `Filter` in place of `iter::Filter`, in the form of `Map`
// above, with two of the three restrictions of Creusot's `Filter` (creusot-std/src/std/iter/
// filter.rs): the closure's captures are used immutably (`P: Fn`, so its state never changes),
// and, in place of a closure without a precondition, the precondition holds on every item the
// inner iterator can yield (`pre_all`; rustc's closure in `layout()` can panic). The closure's
// postcondition need not be precise: `produces` states the count only, the items yielded are at
// most the input items the inner iterator produced, and not which of them.
struct Filter<I, P> {
    iter: I,
    predicate: P,
}

impl<I: thrust_models::Model, P> thrust_models::Model for Filter<I, P> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<P>);
}

#[thrust_macros::context]
impl<I, P> Filter<I, P>
where
    I: Iterator,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::requires(
        I::invariant(iter)
            && Self::reinitialize()
            && Self::pre_all(iter, predicate)
    )]
    #[thrust_macros::ensures(result.0 == iter && result.1 == predicate)]
    fn new(iter: I, predicate: P) -> Filter<I, P> {
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
    I: Iterator,
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
                        && I::invariant((*this).0)
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

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        Self::reinitialize()
            && I::invariant(self.0)
            && Self::pre_all(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as thrust_models::Model>::Ty>, o: Self) -> bool {
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
}

pub struct Wrapped<T> {
    raw: Vec<T>,
}

impl<T: thrust_models::Model> thrust_models::Model for Wrapped<T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}

#[thrust_macros::context]
impl<T> Wrapped<T> {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures((!self).len() == (*self).len() + 1)]
    fn push(&mut self, value: T) {
        self.raw.push(value);
    }

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == raw)]
    fn from_raw(raw: Vec<T>) -> Wrapped<T> {
        Wrapped { raw }
    }
}


// Rewrite (rewrites.md R8): `extend` with a verified body, in place of `Extend::extend`. `self`
// ends as its entry value followed by what `iter` produced before it completed.
#[thrust_macros::context]
impl<T: thrust_models::Model + Copy> Wrapped<T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::requires(J::invariant(iter))]
    #[thrust_macros::ensures(
        exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
               mid: <J as thrust_models::Model>::Ty,
               fin: <J as thrust_models::Model>::Ty|
            J::produces(iter, visited, mid)
                && J::completed(Mut::new(mid, fin))
                && !self == (*self).concat(visited))
    )]
    fn extend_from<J>(&mut self, iter: J)
    where
        J: Iterator<Item = T>,
        <J as thrust_models::Model>::Ty: PartialEq,
    {
        let this = self;
        let mut it = iter;
        J::produces_refl(&it);
        // `pushed` records what `it` produced, so the invariant needs no existential sequence.
        let mut pushed: Vec<T> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: J, this: &mut Wrapped<T>, pushed: Vec<T>, iter: thrust_models::FnParam<J>, self: thrust_models::FnParam<&mut Wrapped<T>>|
                    !this == !self.at_entry()
                        && J::invariant(it)
                        && J::produces(iter.at_entry(), pushed, it)
                        && *this == (*self.at_entry()).concat(pushed)
            );
            this.raw.push(x);
            pushed.push(x);
        }
    }
}


// Rewrite (rewrites.md R8): `collect` with a verified body, in place of `Iterator::collect` into
// the collection: the collection is what the iterator produced before it completed.
#[thrust_macros::context]
#[thrust_macros::requires(J::invariant(iter))]
#[thrust_macros::ensures(
    exists(|visited: Seq<<T as thrust_models::Model>::Ty>,
           mid: <J as thrust_models::Model>::Ty,
           fin: <J as thrust_models::Model>::Ty|
        J::produces(iter, visited, mid)
            && J::completed(Mut::new(mid, fin))
            && result == visited)
)]
fn collect_wrapped<T, J>(iter: J) -> Wrapped<T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
    J: Iterator<Item = T>,
    <J as thrust_models::Model>::Ty: PartialEq,
{
    let mut it = iter;
    J::produces_refl(&it);
    let mut v: Vec<T> = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: J, v: Vec<T>, iter: thrust_models::FnParam<J>|
                J::invariant(it) && J::produces(iter.at_entry(), v, it)
        );
        v.push(x);
    }
    Wrapped::from_raw(v)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!v).len() == (*v).len() + *set + 1)]
fn append_bits(set: &DenseBitSet, v: &mut Wrapped<u32>) {
    v.extend_from(Map::new(set.iter(), thrust_macros::closure!(requires(true), ensures(true), |i: usize| -> u32 { i as u32 })));
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == *set)]
fn collect_bits(set: &DenseBitSet) -> Wrapped<u32> {
    collect_wrapped(Map::new(set.iter(), thrust_macros::closure!(requires(true), ensures(true), |i: usize| -> u32 { i as u32 })))
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() <= *set)]
fn collect_some_bits(set: &DenseBitSet) -> Wrapped<usize> {
    collect_wrapped(Filter::new(set.iter(), thrust_macros::closure!(requires(true), ensures(true), |i: &usize| -> bool { *i > 1 })))
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures((!v).len() == (*v).len() + 1 + *set)]
fn push_then_extend(set: &DenseBitSet, v: &mut Wrapped<u32>, tag: u32) {
    v.push(tag);
    v.extend_from(Map::new(set.iter(), thrust_macros::closure!(requires(true), ensures(true), |i: usize| -> u32 { i as u32 })));
}

fn main() {}
