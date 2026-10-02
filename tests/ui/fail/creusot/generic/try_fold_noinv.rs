//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:804d76744
// `try_fold.rs` with every `invariant!` removed: the loop invariant is left to inference.
use thrust_models::forall;
use thrust_models::model::{Closure, Mut};
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// `try_fold` generic in the iterator `I` and an `FnMut` closure `F`, as std's `Iterator::try_fold`
// is (with the accumulator fixed to `isize` and the `Try` type to `Option<isize>`): the closure's
// contract, stated for every closure state, keeps each `Some` result within `[0, bound]`.
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

// `try_fold` over any iterator: the closure may be called on every accumulator in `[0, bound]` in
// every state, and each `Some` it returns there stays in `[0, bound]`, so a `Some` result does too.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter) && 0 <= init && init <= bound)]
#[thrust_macros::requires(forall(|c: Closure<F>, a: isize, x: <<I as Iterator>::Item as Model>::Ty| (0 <= a && a <= bound) ==> thrust_macros::pre!(c(a, x))))]
#[thrust_macros::requires(forall(|c: Closure<F>, d: Closure<F>, a: isize, x: <<I as Iterator>::Item as Model>::Ty, s: Int| (0 <= a && a <= bound && thrust_macros::post!(Mut::new(c, d)(a, x), Some(s))) ==> (0 <= s && s <= bound)))]
#[thrust_macros::ensures(forall(|s: Int| result == Some(s) ==> (0 <= s && s < bound)))]
fn try_fold<I, F>(iter: I, init: isize, bound: isize, mut f: F) -> Option<isize>
where
    I: Iterator + Model,
    F: FnMut(isize, I::Item) -> Option<isize>,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    let mut it = iter;
    let mut acc = init;
    while let Some(x) = it.next() {
        match f(acc, x) {
            Some(r) => acc = r,
            None => return None,
        }
    }
    Some(acc)
}

fn main() {
    let c = thrust_macros::closure!(
        requires(0 <= a && a <= 100),
        ensures(forall(|s: Int| result == Some(s) ==> (0 <= s && s <= 100))),
        |a: isize, x: isize| -> Option<isize> {
            if 0 <= x && x <= 100 - a { Some(a + x) } else { None }
        },
    );
    let r = try_fold(Range { start: 0, end: 10 }, 0, 100, c);
    assert!(match r { Some(s) => s <= 100, None => true });
}
