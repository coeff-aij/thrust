//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:7f4d6393b
use thrust_models::model::{Closure, Int, Mut, Seq};
use thrust_models::{exists, forall, Ghost, Model};

// The `iterators/map_ext` probe: Creusot's `MapInv`. `Map` carries a ghost history and takes a
// closure `Fn(i64, Ghost<Seq<Int>>) -> i64`, as `drafts/creusot-examples/counter.rs` does. The
// spec differs: the invariant's guard is `next_item` (the item the next call returns) and its
// preservation conjunct is stated over an inner `step` followed by a `next_item`, not over the
// unary `produces1` guard. The closure's precondition is position-dependent, `x ==
// produced.len() + 1`, so the source is `Range { 1, 5 }`: its items are the positions `1..5`.
#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces1(*self, i)))]
    #[thrust_macros::ensures(forall(|i| Self::produces1(!self, i) ==> Self::produces1(*self, i)))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::next_item(*self, i)))]
    #[thrust_macros::ensures(result == None ==> forall(|e| Self::next_item(!self, e) ==> Self::next_item(*self, e)))]
    fn next(&mut self) -> Option<Self::Item>;

    // `collect` delegates to `from_iter`, as in `drafts/creusot-examples/counter.rs`.
    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> Self::produces1(*self, result[k])))]
    fn collect<B: FromIterator<Self::Item>>(&mut self) -> B
    where
        Self: Sized + Model,
        Self::Item: Model,
        <Self as Model>::Ty: PartialEq,
        <Self::Item as Model>::Ty: Model<Ty = <Self::Item as Model>::Ty>,
    {
        B::from_iter(self)
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
    /// `item` is among what `self` may still produce.
    #[thrust_macros::predicate]
    fn produces1(self, item: Self::Item) -> bool;
    /// `item` is the item the next call returns.
    #[thrust_macros::predicate]
    fn next_item(self, item: Self::Item) -> bool;
}

struct Map<I, F> {
    iter: I,
    func: F,
    produced: Ghost<Seq<Int>>,
}

impl<I: Model, F> Model for Map<I, F> {
    type Ty = (<I as Model>::Ty, Closure<F>, Seq<Int>);
}

#[thrust_macros::ensures(result == produced.push(x))]
fn push_produced(produced: Ghost<Seq<Int>>, x: i64) -> Ghost<Seq<Int>> {
    thrust_macros::ghost!(|produced: Ghost<Seq<Int>>, x: i64| -> Seq<Int> { produced.push(x) })
}

#[thrust_macros::context]
impl<I: Iterator<Item = i64> + Model, F: Fn(i64, Ghost<Seq<Int>>) -> i64> Iterator for Map<I, F>
where
    <I as Model>::Ty: PartialEq,
{
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                let r = (self.func)(v, self.produced);
                self.produced = push_produced(self.produced, v);
                Some(r)
            }
            None => None,
        }
    }

    // self.iter.invariant()
    // && forall(|e| self.iter.next_item(e) ==> pre!(self.func(e, self.produced)))
    // && forall(|m, d, e1, e2, h, b| m.step(e1, d) && d.next_item(e2)
    //        && pre!(self.func(e1, h)) && post!(self.func(e1, h), b)
    //        ==> pre!(self.func(e2, h.push(e1))))
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0)
            && forall(|e: Int| !I::next_item(self.0, e) || thrust_macros::pre!((self.1)(e, self.2)))
            && forall(|m: <I as Model>::Ty|
                forall(|d: <I as Model>::Ty|
                    forall(|e1: Int|
                        forall(|e2: Int|
                            forall(|h: Seq<Int>|
                                forall(|b: Int|
                                    !(I::step(m, e1, d)
                                        && I::next_item(d, e2)
                                        && thrust_macros::pre!((self.1)(e1, h))
                                        && thrust_macros::post!((self.1)(e1, h), b))
                                        || thrust_macros::pre!((self.1)(e2, h.push(e1)))))))))
    }

    // self.iter.completed() && *self.func == !self.func && *self.produced == !self.produced
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
            && (*self).2 == (!self).2
    }

    // exists(|i| self.iter.step(i, dist.iter) && pre!(self.func(i, self.produced))
    //    && post!(self.func(i, self.produced), item)
    //    && dist.func == self.func && dist.produced == self.produced.push(i))
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        exists(|i: Int|
            I::step(self.0, i, dist.0)
                && thrust_macros::pre!((self.1)(i, self.2))
                && thrust_macros::post!((self.1)(i, self.2), item)
                && self.1 == dist.1
                && dist.2 == self.2.push(i))
    }

    // exists(|j| self.iter.produces1(j) && pre!(self.func(j, self.produced))
    //    && post!(self.func(j, self.produced), item))
    #[thrust_macros::predicate]
    fn produces1(self, item: Self::Item) -> bool {
        exists(|j: Int|
            I::produces1(self.0, j)
                && thrust_macros::pre!((self.1)(j, self.2))
                && thrust_macros::post!((self.1)(j, self.2), item))
    }

    // exists(|j| self.iter.next_item(j) && pre!(self.func(j, self.produced))
    //    && post!(self.func(j, self.produced), item))
    #[thrust_macros::predicate]
    fn next_item(self, item: Self::Item) -> bool {
        exists(|j: Int|
            I::next_item(self.0, j)
                && thrust_macros::pre!((self.1)(j, self.2))
                && thrust_macros::post!((self.1)(j, self.2), item))
    }
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
    fn produces1(self, item: Self::Item) -> bool {
        self.start <= item && item < self.end
    }

    #[thrust_macros::predicate]
    fn next_item(self, item: Self::Item) -> bool {
        self.start < self.end && item == self.start
    }
}

// `FromIterator<A>` reduced to `from_iter` over `&mut I`, as in `drafts/creusot-examples/counter.rs`.
#[thrust_macros::context]
trait FromIterator<A: Model>: Sized
where
    Self: Model<Ty = Seq<<A as Model>::Ty>>,
    <A as Model>::Ty: Model<Ty = <A as Model>::Ty>,
{
    #[thrust_macros::requires(I::invariant(*iter))]
    #[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> I::produces1(*iter, result[k])))]
    fn from_iter<I: Iterator<Item = A> + Model>(iter: &mut I) -> Self
    where
        <I as Model>::Ty: PartialEq;
}

#[thrust_macros::context]
impl FromIterator<i64> for Vec<i64> {
    fn from_iter<I: Iterator<Item = i64> + Model>(iter: &mut I) -> Vec<i64>
    where
        <I as Model>::Ty: PartialEq,
    {
        let it = iter;
        let mut v: Vec<i64> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: &mut I, v: Vec<i64>, iter: thrust_models::FnParam<&mut I>|
                !it == !iter.at_entry()
                    && I::invariant(*it)
                    && forall(|e: Int| I::produces1(*it, e) ==> I::produces1(*iter.at_entry(), e))
                    && forall(|k: Int| 0 <= k && k < v.len() ==> I::produces1(*iter.at_entry(), v[k]))
            );
            v.push(x);
        }
        v
    }
}

// Creusot's `iterators/map_ext` (its `MapInv`), as a call site over `Range { 1, 5 }` with the
// closure precondition `x == produced.len() + 1`: each produced element is the position. Here the
// checked property is the producibility form, as `counter` uses: every element is one the range
// produces. Unsat: the first element is `1`.
#[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> 1 < result[k] && result[k] < 5))]
fn map_ext() -> Vec<i64> {
    let f = thrust_macros::closure!(
        requires(x == produced.len() + 1),
        ensures(result == x),
        |x: i64, produced: Ghost<Seq<Int>>| -> i64 { x },
    );
    let mut m = Map {
        iter: Range { start: 1, end: 5 },
        func: f,
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    m.collect::<Vec<i64>>()
}

fn main() {}
