//@check-pass
//@compile-flags: --crate-type=lib -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::model::{Mut, Seq};
use thrust_models::{exists, forall, Model};

// The generic `Fuse` of the current Creusot (3620de437, `examples/iterators/07_fuse.rs`): state
// `Option<I>`, its `completed` and `produces`, and the `FusedIterator::is_fused` law.
// fuse_produces_result.rs is the 2022 artifact's version, with state `Result<I, Ghost<I>>`.

mod common;
use common::Iterator;

// Creusot's `FusedIterator`: once `completed`, the iterator produces nothing and stays put.
#[thrust_macros::context]
pub trait FusedIterator: Iterator
where
    Self: Model,
    Self::Item: Model,
{
    #[thrust_macros::law]
    #[thrust_macros::requires(Self::completed(*s))]
    #[thrust_macros::requires(Self::produces(!*s, steps, *next))]
    #[thrust_macros::ensures(steps == Seq::empty())]
    fn is_fused(s: &&mut Self, steps: Seq<<Self::Item as Model>::Ty>, next: &Self) {}
}

pub struct Fuse<I: Iterator>
where
    <I as Iterator>::Item: Model,
{
    pub iter: Option<I>,
}

impl<I: Iterator> Model for Fuse<I>
where
    <I as Iterator>::Item: Model,
{
    type Ty = (Option<<I as Model>::Ty>,);
}

#[thrust_macros::context]
impl<I: Iterator> Iterator for Fuse<I>
where
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <Fuse<I> as Model>::Ty: Model<Ty = <Fuse<I> as Model>::Ty>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            None => None,
            Some(iter) => match iter.next() {
                None => {
                    self.iter = None;
                    None
                }
                x => x,
            },
        }
    }

    // Creusot: `(self.iter == None || exists<it: &mut I> it.completed() && self.iter == Some(*it))
    // && (^self).iter == None`.
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).0 == None
            || exists(|i: <I as Model>::Ty| exists(|j: <I as Model>::Ty|
                (*self).0 == Some(i) && I::completed(Mut::new(i, j)))))
            && (!self).0 == None
    }

    // Creusot's `match self.iter`: from `None` nothing is produced, and from `Some(i)` only to a
    // `Some(k)` that `i` produces. A pattern in a formula cannot bind, so `Some(i)` is an `exists`.
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        (self.0 == None && visited == Seq::empty() && o.0 == self.0)
            || exists(|i: <I as Model>::Ty| exists(|k: <I as Model>::Ty|
                self.0 == Some(i) && o.0 == Some(k) && I::produces(i, visited, k)))
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.0 == None || exists(|i: <I as Model>::Ty| self.0 == Some(i) && I::invariant(i))
    }
}

#[thrust_macros::context]
impl<I: Iterator> FusedIterator for Fuse<I>
where
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <Fuse<I> as Model>::Ty: Model<Ty = <Fuse<I> as Model>::Ty>,
{
}
