//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:804d76744
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, which every impl
// inherits and Thrust checks at each impl (Creusot restates them per impl with empty bodies), and
// `next` with Creusot's contract.
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
{
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::invariant(*a))]
    #[thrust_macros::ensures(Self::produces(*a, Seq::empty(), *a))]
    fn produces_refl(a: &Self) {}

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self) {}

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    fn next(&mut self) -> Option<Self::Item>;
}

#[derive(PartialEq)]
struct Range {
    start: i64,
    end: i64,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }



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
}

// `find`: linear search over a Range for the first item at or above `k`. A returned item is
// bounded and in range; an exhausted search means every item of the range was below `k`.
// No Creusot counterpart; an addition in the spirit of Creusot's examples.
#[thrust_macros::requires(start <= end)]
#[thrust_macros::ensures(
    forall(|x: Int| result == Some(x) ==> (x >= k && start <= x && x < end))
        // Fail twin: `end < k` here (not `<=`) is unsat at `end == k`, where `find` still
        // returns `None` (no item reached `k`). The `x > k` mutation on the other clause, the
        // form `filter`'s fail twin uses, is unsat too, but PCSat's default and share-args
        // configurations both time out disproving it (a quantifier over the `Some` payload);
        // this clause's violation is the one the solver settles quickly, so it is the one kept.
        && (result == None ==> (end < k || end <= start))
)]
fn find(start: i64, end: i64, k: i64) -> Option<i64> {
    let mut it = Range { start, end };
    while let Some(x) = it.next() {
        thrust_macros::invariant!(|it: Range, start: thrust_models::FnParam<i64>, end: thrust_models::FnParam<i64>, k: i64|
            it.start >= start.at_entry()
                && it.end == end.at_entry()
                && (it.start <= start.at_entry() || it.start <= k));
        if x >= k {
            return Some(x);
        }
    }
    None
}

fn main() {}
