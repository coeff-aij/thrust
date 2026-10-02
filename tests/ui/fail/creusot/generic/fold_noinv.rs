//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:804d76744
// `fold.rs` with every `invariant!` removed: the loop invariant is left to inference.
use thrust_models::forall;
use thrust_models::model::{Closure, Mut};
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// `fold` generic in the iterator `I` and an `FnMut` closure `F`, as std's `Iterator::fold` is
// (with the accumulator fixed to `isize`): `acc` stays non-negative because the closure's contract,
// stated for every closure state, keeps each result non-negative on a non-negative accumulator.
// No Creusot counterpart; `main` calls it at `Range` with a concrete closure.

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
    start: isize,
    end: isize,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = isize;

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

// `fold` over any iterator: the closure may be called on every non-negative accumulator in every
// state, and returns a non-negative result there, so the accumulator stays non-negative.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter) && init >= 0)]
#[thrust_macros::requires(forall(|c: Closure<F>, a: isize, x: <<I as Iterator>::Item as Model>::Ty| a >= 0 ==> thrust_macros::pre!(c(a, x))))]
#[thrust_macros::requires(forall(|c: Closure<F>, d: Closure<F>, a: isize, x: <<I as Iterator>::Item as Model>::Ty, r: isize| (a >= 0 && thrust_macros::post!(Mut::new(c, d)(a, x), r)) ==> r >= 0))]
#[thrust_macros::ensures(result > 0)]
fn fold<I, F>(iter: I, init: isize, mut f: F) -> isize
where
    I: Iterator + Model,
    F: FnMut(isize, I::Item) -> isize,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    let mut it = iter;
    let mut acc = init;
    while let Some(x) = it.next() {
        acc = f(acc, x);
    }
    acc
}

fn main() {
    let c = thrust_macros::closure!(
        requires(a >= 0),
        ensures(result >= 0),
        |a: isize, x: isize| -> isize { if x > a { x } else { a } },
    );
    let r = fold(Range { start: 0, end: 10 }, 0, c);
    assert!(r >= 0);
}
