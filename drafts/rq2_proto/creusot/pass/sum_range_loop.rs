//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// Creusot's `examples/iterators/01_range.rs` (3620de437) with its client `sum_range`, with
// Creusot's code and Thrust's annotations: the hand-written `loop` over Creusot's own `Range`,
// concrete. `Range`'s impl is that of `tests/ui/pass/creusot/range.rs`. `snapshot!` is `ghost!`.
// The invariant also states where `iter_old` starts, which Creusot keeps from the snapshot.
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::{FnParam, Ghost, Model};

#[path = "../../../../tests/ui/pass/creusot/auxiliary/common.rs"]
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

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        *self == !self && (*self).start >= (*self).end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        self.end == o.end
            && self.start <= o.start
            && (!(visited.len() > 0) || o.start <= o.end)
            && visited.len() == o.start - self.start
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
    }

    fn next(&mut self) -> Option<isize> {
        if self.start >= self.end {
            None
        } else {
            let r = self.start;
            self.start += 1;
            Some(r)
        }
    }
}

#[thrust_macros::context]
impl Range {
    #[thrust_macros::ensures(result == self)]
    pub fn into_iter(self) -> Self {
        self
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result == n)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    let mut it = Range { start: 0, end: n }.into_iter();
    let iter_old = thrust_macros::ghost!(|it: Range| -> Range { it });
    let mut produced = thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() });
    loop {
        thrust_macros::invariant!(|it: Range, iter_old: Ghost<Range>, produced: Ghost<Seq<Int>>, i: isize, n: FnParam<isize>|
            iter_old.start == 0 && iter_old.end == n.at_entry()
                && Range::produces(iter_old, produced, it)
                && i == produced.len() && i <= n.at_entry());
        match it.next() {
            Some(x) => {
                produced = thrust_macros::ghost!(|produced: Ghost<Seq<Int>>, x: isize| -> Seq<Int> { produced.concat(Seq::singleton(x)) });
                i += 1
            }
            None => break,
        }
    }
    i
}
