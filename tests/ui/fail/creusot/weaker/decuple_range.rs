//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120

// Creusot's `examples/decuple_range`: `(0..10).map(|x| x * 10).collect()` with a closure that is
// defined only below 100. The iterator spec is the step form of `creusot/weaker/map_call.rs`; `Map` is
// the generic adapter from there, used at `Map<Range, closure>`. Creusot uses `map_inv`; the
// closure here does not read the history, so this is plain `map`.
//
// The step form has no history, so what `collect` can promise is that every collected item is
// one the iterator could produce, not its position: the property checked is the range of each
// element, not Creusot's `v[i] == 10 * i` (`creusot/decuple_range.rs` states that one).
use thrust_models::{exists, forall};
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::Model;

// The step form of the iterator specification, Thrust's own: `step(self, item, dist)` relates
// one call of `next` to its successor state, and the unary `produces(self, item)` says `item` is
// among what `self` may still produce. `produces` is monotone under `next`, which makes a guard
// over it inductive where a guard over `step` (one call ahead) is not.
#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    #[thrust_macros::ensures(forall(|i| Self::produces(!self, i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;

    // `collect` delegates to `from_iter`; `&mut self` for the reason given in
    // `traits/collect_visited_seq_i64.rs`.
    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> Self::produces(*self, result[k])))]
    fn collect<B: FromIterator<Self::Item>>(&mut self) -> B
    where
        Self: Sized + Model,
        Self::Item: Model,
        <Self as Model>::Ty: PartialEq,
        <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
    {
        B::from_iter(self)
    }
}

#[derive(PartialEq)]
struct Map<I, F> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,
}

impl<I: Model, F> Model for Map<I, F> {
    type Ty = Map<<I as Model>::Ty, Closure<F>>;
}

#[thrust_macros::context]
impl<I: Iterator + thrust_models::Model, B: thrust_models::Model, F: Fn(I::Item) -> B> Iterator for Map<I, F>
where
    <I as thrust_models::Model>::Ty: PartialEq,
    <I as Iterator>::Item: thrust_models::Model,
    <<I as Iterator>::Item as thrust_models::Model>::Ty:
        thrust_models::Model<Ty = <<I as Iterator>::Item as thrust_models::Model>::Ty> + PartialEq,
{
    type Item = B;
    
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                Some((self.func)(v))
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.iter)
            && forall(|i: <<I as Iterator>::Item as thrust_models::Model>::Ty|
                !I::produces(self.iter, i) || thrust_macros::pre!((self.func)(i)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        exists(|i: <<I as Iterator>::Item as thrust_models::Model>::Ty|
            I::step(self.iter, i, dist.iter)
                && thrust_macros::pre!((self.func)(i))
                && thrust_macros::post!((self.func)(i), item)
                && self.func == dist.func)
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        exists(|j: <<I as Iterator>::Item as thrust_models::Model>::Ty|
            I::produces(self.iter, j)
                && thrust_macros::pre!((self.func)(j))
                && thrust_macros::post!((self.func)(j), item))
    }
}

#[derive(PartialEq)]
struct Range {
    start: isize,
    end: isize,
}

impl thrust_models::Model for Range {
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
        !((*self).start < (*self).end) && *self == !self
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        self.start < self.end
            && self.end == dist.end
            && self.start == item
            && self.start + 1 == dist.start
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        self.start <= item && item < self.end
    }
}

// `FromIterator<A>` reduced to `from_iter` over `&mut I`, as in `traits/collect_visited_seq_i64.rs`.
#[thrust_macros::context]
trait FromIterator<A: Model>: Sized
where
    Self: Model<Ty = Seq<<A as Model>::Ty>>,
    <A as Model>::Ty: Model<Ty = <A as Model>::Ty>,
{
    #[thrust_macros::requires(I::invariant(*iter))]
    #[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> I::produces(*iter, result[k])))]
    fn from_iter<I: Iterator<Item = A> + Model>(iter: &mut I) -> Self
    where
        <I as Model>::Ty: PartialEq;
}

#[thrust_macros::context]
impl FromIterator<isize> for Vec<isize> {
    fn from_iter<I: Iterator<Item = isize> + Model>(iter: &mut I) -> Vec<isize>
    where
        <I as Model>::Ty: PartialEq,
    {
        let it = iter;
        let mut v: Vec<isize> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: &mut I, v: Vec<isize>, iter: thrust_models::FnParam<&mut I>|
                !it == !iter.at_entry()
                    && I::invariant(*it)
                    && forall(|e: Int| I::produces(*it, e) ==> I::produces(*iter.at_entry(), e))
                    && forall(|k: Int| 0 <= k && k < v.len() ==> I::produces(*iter.at_entry(), v[k]))
            );
            v.push(x);
        }
        v
    }
}

// Creusot: `forall i. 0 <= i < v.len() ==> v[i] == i * 10`. Here: every element is `10 * x` for
// some `x` in `0..10`, stated by its bounds. Unsat: `x = 0` gives `0`.
#[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> 1 <= result[k] && result[k] <= 90))]
fn decuple_range() -> Vec<isize> {
    let f = thrust_macros::closure!(
        requires(x < 100),
        ensures(result == x * 10),
        |x: isize| -> isize { x * 10 },
    );
    let mut m = Map {
        iter: Range { start: 0, end: 10 },
        func: f,
    };
    m.collect::<Vec<isize>>()
}

fn main() {}
