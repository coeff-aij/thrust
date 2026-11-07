//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/16_take.rs` (3620de437): `Take` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations. `invariant` states the inner iterator's, which Creusot
// carries as the type invariant of the field; `resolve(self)` in `completed` is spelled out.
use thrust_models::model::{Mut, Seq};
use thrust_models::Model;

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
pub use common::Iterator;

pub struct Take<I> {
    pub iter: I,
    pub n: usize,
}

impl<I: Model> Model for Take<I> {
    type Ty = Take<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<I> Iterator for Take<I>
where
    I: Iterator,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.iter)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        ((*self).n == 0 && (*self).iter == (!self).iter && (*self).n == (!self).n)
            || ((*self).n > 0
                && (*self).n == (!self).n + 1
                && I::completed(Mut::new((*self).iter, (!self).iter)))
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.n == o.n + visited.len() && I::produces(self.iter, visited, o.iter)
    }

    fn next(&mut self) -> Option<I::Item> {
        // Unsat: `n` is not decremented, so `Take` yields more than `n` items.
        if self.n != 0 {
            self.iter.next()
        } else {
            None
        }
    }
}
