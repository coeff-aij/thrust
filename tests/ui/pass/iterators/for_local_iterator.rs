//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` over a local type implementing `Iterator` and `IteratorSpec`, whose invariant names
// `produced`.

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

#[derive(PartialEq)]
struct Counter {
    cur: i64,
    end: i64,
}

impl thrust_models::Model for Counter {
    type Ty = Self;
}

impl Iterator for Counter {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        if self.cur < self.end {
            let x = self.cur;
            self.cur += 1;
            Some(x)
        } else {
            None
        }
    }
}

#[thrust_macros::context]
impl IteratorSpec for Counter {
    #[thrust_macros::predicate]
    fn inv(self) -> bool {
        self.cur <= self.end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Vec<i64>, o: Self) -> bool {
        self.end == o.end
            && self.cur <= o.cur
            && o.cur <= o.end
            && visited.len() == o.cur - self.cur
            && thrust_models::forall(|i: thrust_models::model::Int|
                !(0 <= i && i < visited.len()) || visited[i] == self.cur + i)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        (*self).cur >= (*self).end && *self == !self
    }

    fn produces_refl(a: &Self) {}

    fn produces_trans(
        a: &Self,
        ab: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        b: &Self,
        bc: thrust_models::model::Seq<<Self::Item as thrust_models::Model>::Ty>,
        c: &Self,
    ) {
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(2 * result == n * (n - 1))]
fn sum(n: i64) -> i64 {
    let mut s = 0;
    for x in (Counter { cur: 0, end: n }) {
        thrust_macros::invariant!(|iter: Counter, iter_old: Ghost<Counter>, produced: Ghost<Seq<Int>>, s: i64, n: thrust_models::FnParam<i64>|
            0 <= n.at_entry() && iter_old.cur == 0 && iter_old.end == n.at_entry()
                && 2 * s == produced.len() * (produced.len() - 1));
        s += x;
    }
    s
}

fn main() {
    assert!(sum(4) == 6);
}
