//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:9799dfd7b THRUST_TRY_SPECS=1

use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost};

#[thrust::opaque]
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

impl Iterator for BitIter {
    type Item = usize;
    #[thrust::trusted]
    #[thrust::callable]
    fn next(&mut self) -> Option<usize> {
        None
    }
}

#[thrust_macros::context]
impl IteratorSpec for BitIter {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<usize>, o: Self) -> bool {
        0 <= o && o + visited.len() == self
            && forall(|i: Int| !(0 <= i && i < visited.len()) || 0 <= visited[i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == 0 && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}
// Rewrite (rewrites.md R8): a local `Map` in place of `iter::Map`, evaluation 1's adapter
// (tests/ui/pass/creusot/map.rs) on std.rs's `IteratorSpec`. The model is the inner iterator and
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

    // `next` of the `Iterator` impl below, where the ghost snapshots cannot be written (a
    // `context` impl adds `Model` bounds that std's trait does not have): Creusot's contract of
    // `next` on `Map`, the invariant holds before and after.
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*self))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!self)
            && (result == None ==> <Self as IteratorSpec>::completed(self))
            && forall(|x: <B as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as IteratorSpec>::produces(*self, Seq::singleton(x), !self))
    )]
    fn next_map(&mut self) -> Option<B> {
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

    // The same contract on `Iterator::next`, which `std.rs` gives only for `I: IteratorSpec` with
    // no precondition.
    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(<Self as IteratorSpec>::inv(*it))]
    #[thrust_macros::ensures(
        <Self as IteratorSpec>::inv(!it)
            && (result == None ==> <Self as IteratorSpec>::completed(it))
            && forall(|x: <B as thrust_models::Model>::Ty| result == Some(x)
                ==> <Self as IteratorSpec>::produces(*it, Seq::singleton(x), !it))
    )]
    fn _extern_spec_next(it: &mut Map<I, F>) -> Option<B> {
        <Map<I, F> as Iterator>::next(it)
    }
}

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
        self.next_map()
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
    fn produces(self, visited: Vec<B>, o: Self) -> bool {
        thrust_macros::unnest!(self.1, o.1)
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|fs: Seq<Closure<F>>|
                Self::produces_at(self, visited, o, s, fs)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
    }

    fn produces_refl(a: &Self) {}

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


// Rewrite (rewrites.md R8): `collect` with a verified body, in place of `Iterator::collect` into
// the collection: the collection is what the iterator produced before it completed.
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
fn collect_wrapped<T, J>(iter: J) -> Wrapped<T>
where
    T: thrust_models::Model,
    T::Ty: PartialEq,
    J: IteratorSpec<Item = T>,
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
    Wrapped::from_raw(v)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == *set)]
fn collect_small(set: &DenseBitSet) -> Wrapped<u32> {
    collect_wrapped(Map::new(set.iter(), thrust_macros::closure!(requires(i < 5), ensures(true), |i: usize| -> u32 {
        assert!(i < 5);
        i as u32
    })))
}

fn main() {}
