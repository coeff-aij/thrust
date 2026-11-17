//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `examples/iterators/11_repeat.rs` (3620de437): `Repeat` and its `Iterator` impl, with
// Creusot's code and Thrust's annotations. Creusot's `Self::Item::clone.postcondition((&self.element,), v)`
// is `v == self.element`, std.rs's contract of `Clone::clone` (`post!` of `clone` at the type
// parameter `A` does not verify here).
use thrust_models::model::{Int, Seq};
use thrust_models::{forall, Model};

#[path = "../../pass/creusot/auxiliary/common.rs"]
mod common;
use common::Iterator;

pub struct Repeat<A> {
    pub element: A,
}

impl<A: Model> Model for Repeat<A> {
    type Ty = Repeat<<A as Model>::Ty>;
}

#[thrust_macros::context]
impl<A: Clone + Model> Iterator for Repeat<A> {
    type Item = A;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        false
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self == o
            && forall(|i: Int| {
                !(0 <= i && i < visited.len())
                    || visited[i] == self.element
            })
    }

    fn next(&mut self) -> Option<A> {
        // Unsat: `completed` is false, so `next` returning `None` breaks its contract.
        None
    }
}
