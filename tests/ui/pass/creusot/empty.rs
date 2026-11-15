//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/09_empty.rs` (3620de437): `Empty` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations. `resolve(self)` in `completed` is `*self == !self`.
use thrust_models::model::Seq;
use thrust_models::Model;

#[path = "auxiliary/common.rs"]
mod common;
use common::Iterator;

pub struct Empty<T>(std::marker::PhantomData<T>);

impl<T: Model> Model for Empty<T> {
    type Ty = Empty<<T as Model>::Ty>;
}

#[thrust_macros::context]
impl<T: Model> Iterator for Empty<T> {
    type Item = T;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        visited == Seq::empty() && self == o
    }

    fn next(&mut self) -> Option<T> {
        None
    }
}
