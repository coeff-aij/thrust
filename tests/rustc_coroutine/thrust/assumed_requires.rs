//! The wrappers of `univariant_biased.rs`'s fallback (rustc_abi `layout.rs`): each calls a callee
//! whose `requires` the solver does not answer at that call, with that `requires` assumed, where an
//! `assume!` at the call cannot name the closure's type. Their bodies are checked; only the
//! callee's `requires` is assumed. They are a module of their own so that a root selecting
//! `case_study::iter` does not verify them; only the roots that call them select them.
//! `map_new_assumed` stays in `iter.rs`, because `layout()` calls it.

use crate::thrust_models;
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall};

use crate::IteratorSpec;
use crate::case_study::USize;
use super::iter::{Filter, IterAllSpec, iter_all};

// `Filter::new`, its `requires` assumed (a goal of `univariant_biased` the solver does not answer).
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.0 == iter && result.1 == predicate)]
pub fn filter_new_assumed<I, P>(iter: I, predicate: P) -> Filter<I, P>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
{
    thrust_macros::assume!(|iter: I, predicate: P| I::inv(iter)
        && Filter::<I, P>::reinitialize()
        && Filter::<I, P>::pre_all(iter, predicate));
    Filter::new(iter, predicate)
}

// `Filter::next`, its `requires` (the filter's invariant) assumed (goals of `univariant_biased`
// the solver does not answer); the `ensures` is `next`'s.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    <Filter<I, P> as IteratorSpec>::inv(!it)
        && (result == None ==> <Filter<I, P> as IteratorSpec>::completed(it))
        && forall(|x: <I::Item as thrust_models::Model>::Ty| result == Some(x)
            ==> (<Filter<I, P> as IteratorSpec>::produces(*it, Seq::singleton(x), !it)
                && exists(|s: Seq<<I::Item as thrust_models::Model>::Ty>|
                    I::produces((*it).0, s.push(x), (!it).0))))
)]
pub fn filter_next_assumed<I, P>(it: &mut Filter<I, P>) -> Option<I::Item>
where
    I: IteratorSpec,
    P: Fn(&I::Item) -> bool,
    I::Item: thrust_models::Model,
{
    thrust_macros::assume!(|it: &mut Filter<I, P>| <Filter<I, P> as IteratorSpec>::inv(*it));
    it.next()
}

// `iter_all`, its `requires` assumed (a goal of `univariant_biased` the solver does not answer); the `ensures` is
// `iter_all`'s.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
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
pub fn iter_all_assumed<I, F>(iter: I, f: F) -> bool
where
    I: IteratorSpec,
    F: Fn(I::Item) -> bool,
    I::Item: thrust_models::Model + Copy,
    // A bound `iter_all` has through its `#[context]`.
    <I as thrust_models::Model>::Ty: PartialEq,
{
    thrust_macros::assume!(|iter: I, f: F| I::inv(iter) && IterAllSpec::<I, F>::pre_all(iter, f));
    iter_all(iter, f)
}

// `Option::map_or`, its `requires` (std.rs) assumed (`univariant_biased`'s sort key closure, whose
// three `map_or` goals the solver does not answer); the `ensures` is `map_or`'s.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (opt == None && result == default)
        || exists(|i: <T as thrust_models::Model>::Ty| opt == Some(i) && thrust_macros::post!(f(i), result))
)]
pub fn map_or_assumed<T, U, F>(opt: Option<T>, default: U, f: F) -> U
where
    T: thrust_models::Model,
    U: thrust_models::Model,
    F: FnOnce(T) -> U,
{
    thrust_macros::assume!(|opt: Option<T>, f: F|
        opt == None || exists(|i: <T as thrust_models::Model>::Ty| opt == Some(i) && thrust_macros::pre!(f(i))));
    opt.map_or(default, f)
}

// `Option::map`, its `requires` (std.rs) assumed (`univariant_biased`'s `alignment_group_key`, whose
// `map` goal the solver does not answer); the `ensures` is `map`'s.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (opt == None && result == None)
        || exists(|i: <T as thrust_models::Model>::Ty, j: <U as thrust_models::Model>::Ty|
            opt == Some(i) && thrust_macros::post!(f(i), j) && result == Some(j))
)]
pub fn map_assumed<T, U, F>(opt: Option<T>, f: F) -> Option<U>
where
    T: thrust_models::Model,
    U: thrust_models::Model,
    F: FnOnce(T) -> U,
{
    thrust_macros::assume!(|opt: Option<T>, f: F|
        opt == None || exists(|i: <T as thrust_models::Model>::Ty| opt == Some(i) && thrust_macros::pre!(f(i))));
    opt.map(f)
}

// `<[T]>::sort_by_key`, its `requires` (std.rs) assumed (`univariant_biased`'s sort of the fields
// that are not the tail, whose `sort_by_key` goal the solver does not answer); the `ensures` is
// `sort_by_key`'s.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (!slice).len() == (*slice).len()
        && exists(|p: Seq<Int>|
            p.len() == (*slice).len()
                && forall(|i: Int|
                    (0 <= i && i < (*slice).len())
                        ==> (0 <= p[i] && p[i] < (*slice).len() && (!slice)[i] == (*slice)[p[i]]))
                && forall(|i: Int, j: Int|
                    (0 <= i && i < (*slice).len() && 0 <= j && j < (*slice).len() && i != j)
                        ==> p[i] != p[j])
                && forall(|j: Int|
                    (0 <= j && j < (*slice).len())
                        ==> exists(|i: Int| 0 <= i && i < (*slice).len() && p[i] == j)))
)]
pub fn sort_by_key_assumed<T, K, F>(slice: &mut [T], f: F)
where
    T: thrust_models::Model,
    K: Ord,
    F: FnMut(&T) -> K,
{
    thrust_macros::assume!(|slice: &mut [T], f: F|
        forall(|c: Closure<F>, i: Int|
            (thrust_macros::hist_inv!(f, c) && 0 <= i && i < (*slice).len())
                ==> thrust_macros::pre!(c(&(*slice)[i]))));
    slice.sort_by_key(f)
}

// `Iterator::max`, its `requires` (the iterator's invariant, std_specs.rs) assumed
// (a goal of `univariant_biased` the solver does not answer); `max`'s `ensures` states nothing of the result.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
pub fn max_assumed<I>(it: I) -> Option<I::Item>
where
    I: IteratorSpec,
    I::Item: thrust_models::Model + Ord,
{
    thrust_macros::assume!(|it: I| I::inv(it));
    it.max()
}
