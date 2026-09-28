//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:12308225c
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// Creusot's `common.rs`/`range.rs` iterator spec: ternary `produces(self, visited, o)`, `completed`,
// and the laws as ensures on `next`. Seq literals are bound before use (`t == s.push(i) ==> ..`).
#[thrust_macros::context]
trait Iterator
where
    Self: Model,
    Self::Item: Model,
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
    <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
{
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    // `produces_refl` at the entry state and `produces_trans` with a singleton second leg,
    // applied at every `next` instead of called; the singleton instance is kept for concrete loops.
    #[thrust_macros::ensures(Self::produces(*self, Seq::empty(), *self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, Seq::singleton(i), !self)))]
    #[thrust_macros::ensures(forall(|a: <Self as Model>::Ty| forall(|s: Seq<<Self::Item as Model>::Ty>| forall(|i|
        result == Some(i) && Self::produces(a, s, *self) ==> Self::produces(a, s.push(i), !self)))))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool;
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
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.resolve() && self.start >= self.end
        *self == !self && (*self).start >= (*self).end
    }

    #[thrust_macros::predicate]
    fn produces(self, visited: Seq<<Self::Item as Model>::Ty>, o: Self) -> bool {
        // self.end == o.end && self.start <= o.start
        // && (visited.len() > 0 ==> o.start <= o.end)
        // && visited.len() == o.start - self.start
        // && forall i. 0 <= i < visited.len() ==> visited[i] == self.start + i
        self.end == o.end
            && self.start <= o.start
            && (!(visited.len() > 0) || o.start <= o.end)
            && visited.len() == o.start - self.start
            && forall(|i: Int| !(0 <= i && i < visited.len()) || visited[i] == self.start + i)
    }
}

// `filter`: collects every item of a Range at or above `k`. Every collected item meets the
// bound, and the result is no longer than the range itself.
// No Creusot counterpart; an addition in the spirit of Creusot's examples.
#[thrust_macros::requires(start <= end)]
#[thrust_macros::ensures(
    forall(|j: Int| (0 <= j && j < result.len()) ==> result[j] >= k)
        && result.len() <= end - start
)]
fn filter(start: i64, end: i64, k: i64) -> Vec<i64> {
    let mut it = Range { start, end };
    let mut out: Vec<i64> = Vec::new();
    while let Some(x) = it.next() {
        thrust_macros::invariant!(|it: Range, out: Vec<i64>, start: thrust_models::FnParam<i64>, end: thrust_models::FnParam<i64>, k: i64|
            it.start >= start.at_entry()
                && it.start <= end.at_entry()
                && it.end == end.at_entry()
                && out.len() <= it.start - start.at_entry()
                && forall(|j: Int| (0 <= j && j < out.len()) ==> out[j] >= k));
        if x >= k {
            out.push(x);
        }
    }
    out
}

fn main() {}
