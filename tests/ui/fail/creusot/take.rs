//@error-in-other-file: Unsat
//@compile-flags: --crate-type=lib -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
use thrust_models::forall;
use thrust_models::model::{Int, Mut, Seq};
use thrust_models::Model;

#[path = "../../pass/creusot/common.rs"]
mod common;
use common::Iterator;

pub struct Take<I: Iterator>
where
    <I as Iterator>::Item: Model,
{
    pub iter: I,
    pub n: usize,
}

impl<I: Iterator> Model for Take<I>
where
    <I as Iterator>::Item: Model,
{
    type Ty = (<I as Model>::Ty, <usize as Model>::Ty);
}

#[thrust_macros::context]
impl<I> Iterator for Take<I>
where
    I: Iterator,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty>,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
    <Take<I> as Model>::Ty: Model<Ty = <Take<I> as Model>::Ty>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).1 == 0 && (*self).0 == (!self).0 && (*self).1 == (!self).1)
            || ((*self).1 > 0
                && (*self).1 == (!self).1 + 1
                && I::completed(Mut::new((*self).0, (!self).0)))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.1 == o.1 + visited.len() + 1 && I::produces(self.0, visited, o.0)
    }
}
