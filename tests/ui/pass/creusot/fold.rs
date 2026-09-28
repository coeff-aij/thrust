//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:12308225c
use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// A hand-written fold over `range.rs`'s Range: `acc` stays non-negative because the closure's
// contract keeps every result non-negative on non-negative inputs. No Creusot counterpart; an
// addition in the spirit of Creusot's examples.

// Creusot's `common.rs`, the iterator specification every case shares: the trait predicates
// `produces(self, visited, o)`, `completed` and `invariant` (`true` unless the impl says otherwise),
// the laws `produces_refl` and `produces_trans` in Creusot's concatenation form, proved by each
// impl, and `next` with Creusot's contract.
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
    fn produces_refl(a: &Self);

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::produces(*a, ab, *b))]
    #[thrust_macros::requires(Self::produces(*b, bc, *c))]
    #[thrust_macros::ensures(Self::produces(*a, ab.concat(bc), *c))]
    fn produces_trans(a: &Self, ab: Seq<<Self::Item as Model>::Ty>, b: &Self, bc: Seq<<Self::Item as Model>::Ty>, c: &Self);

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

    fn produces_refl(a: &Range) {}

    fn produces_trans(a: &Range, ab: Seq<<Self::Item as Model>::Ty>, b: &Range, bc: Seq<<Self::Item as Model>::Ty>, c: &Range) {}

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

// `fold` over a `Range`: the closure is defined on every `(a, x)` with `a >= 0` and `x` in
// `[start, end)`, and every result it returns on non-negative inputs is itself non-negative, so
// the accumulator stays non-negative throughout.
#[thrust_macros::requires(0 <= start && start <= end && init >= 0)]
#[thrust_macros::requires(forall(|a: i64| forall(|x: i64| (a >= 0 && start <= x && x < end) ==> thrust_macros::pre!(f(a, x)))))]
#[thrust_macros::requires(forall(|a: i64| forall(|x: i64| forall(|r: i64| (a >= 0 && x >= 0) ==> (thrust_macros::post!(f(a, x), r) ==> r >= 0)))))]
#[thrust_macros::ensures(result >= 0)]
#[thrust_macros::context]
fn fold<F: Fn(i64, i64) -> i64>(start: i64, end: i64, init: i64, f: F) -> i64 {
    let mut it = Range { start, end };
    let mut acc = init;
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: Range, acc: i64, f: thrust_models::FnParam<F>|
            it.start >= 0
                && it.start <= it.end
                && acc >= 0
                && forall(|a: i64| forall(|x: i64| (a >= 0 && it.start <= x && x < it.end) ==> thrust_macros::pre!(f.at_entry()(a, x))))
                && forall(|a: i64| forall(|x: i64| forall(|r: i64| (a >= 0 && x >= 0) ==> (thrust_macros::post!(f.at_entry()(a, x), r) ==> r >= 0))))
        );
        acc = f(acc, x);
    }
    acc
}

fn main() {}
