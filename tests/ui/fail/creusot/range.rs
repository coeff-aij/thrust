//@error-in-other-file: Unsat
//@compile-flags: --crate-type=lib -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

#[path = "../../pass/creusot/common.rs"]
mod common;
use common::Iterator;

struct Range {
    pub start: isize,
    pub end: isize,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = isize;

    fn next(&mut self) -> Option<isize> {
        if self.start >= self.end {
            None
        } else {
            let r = self.start;
            self.start += 1;
            Some(r)
        }
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // Unsat: `next` returns `None` already at `start == end`, where this `completed` is false.
        *self == !self && (*self).start > (*self).end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.end == o.end
            && self.start <= o.start
            && (!(visited.len() > 0) || o.start <= o.end)
            && visited.len() == o.start - self.start
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
    }
}

#[thrust_macros::context]
impl Range {
    #[thrust_macros::ensures(result == self)]
    pub fn into_iter(self) -> Self {
        self
    }
}
