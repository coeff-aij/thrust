//! The wrappers of `univariant_biased.rs`'s fallback (rustc_abi `layout.rs`): each calls a callee
//! whose `requires` the solver does not answer at that call, with that `requires` assumed, where an
//! `assume!` at the call cannot name the type of the iterator or of the filter's closure. Their bodies are checked; only the
//! callee's `requires` is assumed. They are a module of their own so that a root selecting
//! `case_study::iter` does not verify them; only the roots that call them select them.
//! `map_new_assumed` stays in `iter.rs`, because `layout()` calls it.

use crate::thrust_models;
use thrust_models::model::Seq;
use thrust_models::{exists, forall};

use crate::IteratorSpec;
use crate::case_study::USize;
use super::iter::Filter;

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
