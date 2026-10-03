//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
// `filter.rs` with every `invariant!` removed: the loop invariant is left to inference.
use thrust_models::{exists, forall};
use thrust_models::model::{Closure, Mut};
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// `filter` collected into a `Vec`, generic in the iterator `I` and an `FnMut` predicate `P`, as
// std's `iter.filter(p).collect::<Vec<_>>()` is (with the predicate taking the item by value,
// `I::Item: Copy`, where std passes `&I::Item`).
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

// `filter` collected into a `Vec` over any iterator: the predicate may be called on every item
// in every state, and every collected item is one on which some call of it returned `true`.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(iter))]
#[thrust_macros::requires(forall(|c: Closure<P>, x: <<I as Iterator>::Item as Model>::Ty| thrust_macros::pre!(c(x))))]
#[thrust_macros::ensures(forall(|k: Int| (0 <= k && k < result.len()) ==> exists(|c: Closure<P>, d: Closure<P>| thrust_macros::post!(Mut::new(c, d)(result[k]), true))))]
fn filter<I, P>(iter: I, mut p: P) -> Vec<I::Item>
where
    I: Iterator + Model,
    P: FnMut(I::Item) -> bool,
    <I as Iterator>::Item: Model + Copy,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    let mut it = iter;
    let mut out: Vec<I::Item> = Vec::new();
    while let Some(x) = it.next() {
        if p(x) {
            out.push(x);
        }
    }
    out
}

fn main() {
    let c = thrust_macros::closure!(
        ensures(result == (x >= 5)),
        |x: isize| -> bool { x >= 5 },
    );
    let v = filter(Range { start: 0, end: 10 }, c);
    if v.len() > 0 {
        assert!(v[0] >= 5);
    }
}
