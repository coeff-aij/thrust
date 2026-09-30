//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:9799dfd7b THRUST_TRY_SPECS=1

use std::iter;
use std::marker::PhantomData;
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost};
// local to the case study: `Map` is modelled as Creusot's (tests/ui/pass/creusot/map.rs) is, by
// the inner iterator and the closure state
impl<I: thrust_models::Model, F> thrust_models::Model for iter::Map<I, F> {
    type Ty = (<I as thrust_models::Model>::Ty, Closure<F>);
}

// local to the case study: `Map<I, F>` for a signature of a specification, where a bare `F`
// would be read as its `Closure` model a second time
trait MapOf {
    type Out;
}

impl<I, F> MapOf for (I, F) {
    type Out = iter::Map<I, F>;
}

// local to the case study: the predicates of `Map`, which cannot be an inherent impl of a
// foreign type; Creusot's `next_precondition`, `preservation_inv`, `reinitialize` and `produces`
// over the input items `s` and closure states `fs`
struct MapSpec<I, F>(PhantomData<(I, F)>);

#[thrust_macros::context]
impl<I, B, F> MapSpec<I, F>
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
    fn produces_at(s0: I, f0: F, visited: Vec<B>, o0: I, f1: F, s: Seq<<I::Item as thrust_models::Model>::Ty>, fs: Seq<F>) -> bool {
        thrust_macros::unnest!(f0, f1)
            && s.len() == visited.len()
            && I::produces(s0, s, o0)
            && fs.len() == visited.len() + 1
            && fs[0] == f0
            && fs[visited.len()] == f1
            && forall(|k: Int|
                !(0 <= k && k < visited.len())
                    || (thrust_macros::unnest!(f0, fs[k])
                        && thrust_macros::post!(Mut::new(fs[k], fs[k + 1])(s[k]), visited[k])))
    }

    // `produces_at` of the joined witnesses: the input items concatenated and the closure states
    // joined at their shared state.
    #[thrust_macros::ensures(forall(|sab: Seq<<I::Item as thrust_models::Model>::Ty>| forall(|sbc: Seq<<I::Item as thrust_models::Model>::Ty>|
        forall(|fab: Seq<Closure<F>>| forall(|fbc: Seq<Closure<F>>|
        !(Self::produces_at(a.0, a.1, ab, b.0, b.1, sab, fab) && Self::produces_at(b.0, b.1, bc, c.0, c.1, sbc, fbc))
            || Self::produces_at(a.0, a.1, ab.concat(bc), c.0, c.1, sab.concat(sbc), fab.subsequence(0, ab.len()).concat(fbc)))))))]
    fn produces_trans_at(
        a: Ghost<<(I, F) as MapOf>::Out>,
        ab: Ghost<Seq<<<iter::Map<I, F> as Iterator>::Item as thrust_models::Model>::Ty>>,
        b: Ghost<<(I, F) as MapOf>::Out>,
        bc: Ghost<Seq<<<iter::Map<I, F> as Iterator>::Item as thrust_models::Model>::Ty>>,
        c: Ghost<<(I, F) as MapOf>::Out>,
    ) {
    }
}

// local to the case study
#[thrust_macros::context]
impl<I, B, F> IteratorSpec for iter::Map<I, F>
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
        MapSpec::<I, F>::reinitialize()
            && MapSpec::<I, F>::preservation_inv(self.0, self.1)
            && I::inv(self.0)
            && MapSpec::<I, F>::next_precondition(self.0, self.1)
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<B>, o: Self) -> bool {
        thrust_macros::unnest!(self.1, o.1)
            && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>| exists(|fs: Seq<Closure<F>>|
                MapSpec::<I, F>::produces_at(self.0, self.1, visited, o.0, o.1, s, fs)))
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
        MapSpec::<I, F>::produces_trans_at(ga, gab, gb, gbc, gc);
        // Keeps the parameters live at the snapshots above.
        let _live = (a, &ab, b, &bc, c);
    }
}

// local to the case study: an iterator is its own `into_iter`
#[thrust_macros::context]
impl<I, B, F> IntoIteratorSpec for iter::Map<I, F>
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
    fn into_iter_is(self, it: Self) -> bool {
        self.0 == it.0 && self.1 == it.1
    }
}

// local to the case study: the map is built with the invariant of Creusot's `Map`, which gives
// the closure's precondition on every item the iterator yields
#[thrust::extern_spec_fn]
#[thrust_macros::requires(
    I::inv(it)
        && MapSpec::<I, F>::reinitialize()
        && MapSpec::<I, F>::preservation_inv(it, f)
        && MapSpec::<I, F>::next_precondition(it, f)
)]
#[thrust_macros::ensures(result.0 == it && result.1 == f)]
fn _extern_spec_iterator_map<I, B, F>(it: I, f: F) -> <(I, F) as MapOf>::Out
where
    I: IteratorSpec,
    B: thrust_models::Model,
    F: FnMut(I::Item) -> B,
    I::Item: thrust_models::Model,
    <I::Item as thrust_models::Model>::Ty: thrust_models::Model<Ty = <I::Item as thrust_models::Model>::Ty> + PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
    <B as thrust_models::Model>::Ty: PartialEq,
{
    <I as Iterator>::map(it, f)
}


pub struct Wrapped<T> {
    raw: Vec<T>,
}

impl<T: thrust_models::Model> thrust_models::Model for Wrapped<T> {
    type Ty = <[T] as thrust_models::Model>::Ty;
}
// local to the case study: what a collection built by `collect` says of the items it took;
// `stopped` is a fallible collection that stopped at a failing item, before the iterator ended
#[thrust_macros::context]
trait FromIteratorSpec<A>: FromIterator<A> + thrust_models::Model
where
    A: thrust_models::Model,
{
    #[thrust_macros::predicate]
    fn from_iter_post(prod: Vec<A>, res: Self) -> bool;

    #[thrust_macros::predicate]
    fn stopped(self) -> bool;
}
// local to the case study
#[thrust_macros::context]
impl<T: thrust_models::Model> FromIteratorSpec<T> for Wrapped<T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn from_iter_post(prod: Vec<T>, res: Self) -> bool {
        prod == res
    }

    #[thrust_macros::predicate]
    fn stopped(self) -> bool {
        false
    }
}

impl<T> FromIterator<T> for Wrapped<T> {
    fn from_iter<J: IntoIterator<Item = T>>(iter: J) -> Self {
        Wrapped { raw: Vec::from_iter(iter) }
    }
}
// local to the case study: `collect` exhausts the iterator, or stops at a failing item
#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    exists(|visited: Seq<<I::Item as thrust_models::Model>::Ty>, mid: <I as thrust_models::Model>::Ty, fin: <I as thrust_models::Model>::Ty|
        I::produces(it, visited, mid)
            && I::completed(Mut::new(mid, fin))
            && B::from_iter_post(visited, result))
        || B::stopped(result)
)]
fn _extern_spec_iterator_collect<I, B>(it: I) -> B
where
    I: IteratorSpec,
    I::Item: thrust_models::Model,
    I::Ty: PartialEq,
    <I::Item as thrust_models::Model>::Ty: PartialEq,
    B: FromIteratorSpec<I::Item>,
    B::Ty: PartialEq,
{
    <I as Iterator>::collect::<B>(it)
}

pub struct SliceIter<'a, T> {
    raw: &'a [T],
    pos: usize,
}

impl<'a, T: thrust_models::Model> thrust_models::Model for SliceIter<'a, T> {
    type Ty = (<&'a [T] as thrust_models::Model>::Ty, Int);
}

impl<'a, T> Iterator for SliceIter<'a, T> {
    type Item = &'a T;

    #[thrust::trusted]
    #[thrust::callable]
    fn next(&mut self) -> Option<&'a T> {
        None
    }
}

#[thrust_macros::context]
impl<'a, T: thrust_models::Model> IteratorSpec for SliceIter<'a, T>
where
    T::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        0 <= self.1 && self.1 <= self.0.len()
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<&'a T>, o: Self) -> bool {
        self.0 == o.0
            && self.1 <= o.1
            && o.1 <= self.0.len()
            && visited.len() == o.1 - self.1
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == &self.0[self.1 + i])
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).1 >= (*self).0.len() && *self == !self
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

fn iter_of(raw: &[u32]) -> SliceIter<'_, u32> {
    SliceIter { raw, pos: 0 }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == (*xs).len() + 1)]
fn collect_all(xs: &[u32]) -> Wrapped<&u32> {
    iter_of(xs).collect()
}

fn main() {}
