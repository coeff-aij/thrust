//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// Creusot's `examples/iterators/07_fuse.rs` (3620de437): `Fuse`, its `Iterator` impl and the
// `FusedIterator` law, with Creusot's code and Thrust's annotations. `invariant` states the inner
// iterator's, which Creusot carries as the type invariant of the field.
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, Model};

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
use common::Iterator;

pub struct Fuse<I> {
    pub iter: Option<I>,
}

impl<I: Model> Model for Fuse<I> {
    type Ty = Fuse<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<I: Iterator> Iterator for Fuse<I> {
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.iter == None || exists(|i: <I as Model>::Ty| self.iter == Some(i) && I::invariant(i))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).iter == None
            || exists(|i: <I as Model>::Ty| exists(|j: <I as Model>::Ty|
                (*self).iter == Some(i) && I::completed(Mut::new(i, j)))))
            && (!self).iter == None
    }

    // Creusot's `match self.iter` as a disjunction: a pattern in a formula cannot bind a
    // variable, so the `Some(i)` arm is an `exists`.
    #[thrust_macros::predicate]
    fn produces(self, prod: Seq<<Self::Item as Model>::Ty>, other: Self) -> bool {
        (self.iter == None && prod == Seq::empty() && other.iter == self.iter)
            || exists(|i: <I as Model>::Ty| exists(|i2: <I as Model>::Ty|
                self.iter == Some(i) && other.iter == Some(i2) && I::produces(i, prod, i2)))
    }

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            None => None,
            Some(iter) => match iter.next() {
                // Unsat: the inner iterator is kept after it completes, so `completed` (which
                // requires `(!self).iter == None`) is refuted.
                None => None,
                x => x,
            },
        }
    }
}

#[thrust_macros::context]
pub trait FusedIterator: Iterator
where
    Self::Item: Model,
{
    #[thrust_macros::law]
    #[thrust_macros::requires(Self::completed(*s))]
    #[thrust_macros::requires(Self::produces(!*s, steps, *next))]
    #[thrust_macros::ensures(steps == Seq::empty())]
    fn is_fused(s: &&mut Self, steps: Seq<<Self::Item as Model>::Ty>, next: &Self) {}
}

#[thrust_macros::context]
impl<I: Iterator> FusedIterator for Fuse<I> {}
