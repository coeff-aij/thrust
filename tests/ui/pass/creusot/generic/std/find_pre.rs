//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300
use thrust_models::{exists, forall};
use thrust_models::model::{Closure, Mut};
use thrust_models::model::{Int, Seq};
use thrust_models::Model;

// `find.rs` without `find`'s postcondition: `find` calls `try_fold` with `check`, whose
// precondition is inferred. `try_fold` requires it at every state of `check`, which only `find`'s
// own precondition on the predicate establishes, through the blocks between `find`'s entry and
// the call.

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

#[derive(PartialEq)]
enum ControlFlow<B> {
    Continue(()),
    Break(B),
}

impl<B: Model> Model for ControlFlow<B> {
    type Ty = ControlFlow<<B as Model>::Ty>;
}

// std's default `try_fold` with the `Try` type fixed to `ControlFlow<I::Item>`: the closure may be
// called on every item in every state, and a `Break` result is one some call of it returned from a
// state reachable from `f`.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(*iter))]
#[thrust_macros::requires(forall(|c: Closure<F>, x: <<I as Iterator>::Item as Model>::Ty| thrust_macros::pre!(c(x))))]
#[thrust_macros::ensures(forall(|v: <<I as Iterator>::Item as Model>::Ty| result == ControlFlow::Break(v) ==> exists(|c: Closure<F>, d: Closure<F>, x: <<I as Iterator>::Item as Model>::Ty| thrust_macros::hist_inv!(f, c) && thrust_macros::post!(Mut::new(c, d)(x), ControlFlow::Break(v)))))]
fn try_fold<I, F>(iter: &mut I, f: F) -> ControlFlow<I::Item>
where
    I: Iterator + Model,
    F: FnMut(I::Item) -> ControlFlow<I::Item>,
    <I as Iterator>::Item: Model,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    let it = iter;
    let mut g = f;
    while let Some(x) = it.next() {
        thrust_macros::invariant!(
            |it: &mut I, g: F, f: thrust_models::FnParam<F>|
            I::invariant(*it)
                && thrust_macros::hist_inv!(f.at_entry(), g)
                && forall(|c: Closure<F>, x: <<I as Iterator>::Item as Model>::Ty| thrust_macros::pre!(c(x)))
        );
        match g(x) {
            ControlFlow::Continue(()) => {}
            ControlFlow::Break(b) => return ControlFlow::Break(b),
        }
    }
    ControlFlow::Continue(())
}

// std's `find`: `check` breaks with an item exactly when the predicate accepts it.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant(*iter))]
#[thrust_macros::requires(forall(|c: Closure<P>, x: <<I as Iterator>::Item as Model>::Ty| thrust_macros::pre!(c(x))))]
fn find<I, P>(iter: &mut I, mut predicate: P) -> Option<I::Item>
where
    I: Iterator + Model,
    P: FnMut(I::Item) -> bool,
    <I as Iterator>::Item: Model + Copy,
    <I as Model>::Ty: Model<Ty = <I as Model>::Ty> + PartialEq,
    <<I as Iterator>::Item as Model>::Ty: Model<Ty = <<I as Iterator>::Item as Model>::Ty> + PartialEq,
{
    // `check` owns the predicate, so its states are related as the predicate's are.
    let check = thrust_macros::closure!(
        captures(predicate: &mut P),
        hist_inv(thrust_macros::hist_inv!(*predicate, !predicate)),
        move |x: I::Item| -> ControlFlow<I::Item> {
            if predicate(x) { ControlFlow::Break(x) } else { ControlFlow::Continue(()) }
        },
    );
    match try_fold(iter, check) {
        ControlFlow::Break(x) => Some(x),
        ControlFlow::Continue(()) => None,
    }
}

fn main() {}
