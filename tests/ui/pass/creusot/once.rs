//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/10_once.rs` (3620de437): `Once` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations. `resolve(self)` in `completed` is `*self == !self`.
use thrust_models::model::Seq;
use thrust_models::{exists, Model};

#[path = "auxiliary/common.rs"]
mod common;
use common::Iterator;

pub struct Once<T>(pub Option<T>);

impl<T: Model> Model for Once<T> {
    type Ty = Once<<T as Model>::Ty>;
}

#[thrust_macros::context]
impl<T: Model> Iterator for Once<T> {
    type Item = T;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).0 == None && *self == !self
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        (visited == Seq::empty() && self == o)
            || exists(|e: <T as Model>::Ty| {
                self.0 == Some(e) && visited == Seq::singleton(e) && o.0 == None
            })
    }

    fn next(&mut self) -> Option<T> {
        self.0.take()
    }
}
