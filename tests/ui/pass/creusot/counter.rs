//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:804d76744
use thrust_models::model::{Closure, Int, Mut, Seq, UInt};
use thrust_models::{exists, forall, Ghost, Model};

// Creusot's `examples/counter`: `v.iter().map_inv(|x, _prod| { cnt += 1; *x }).collect()`, where
// the closure's precondition `cnt == _prod.len()` reads the history. The iterator spec is the
// step form with a unary `produces` guard; `Map` carries Creusot's `MapInv` ghost `produced`
// and takes an `FnMut(u32, Ghost<Seq<UInt>>)`. The source is a `Range` instead of `v.iter()`.
//
// The step form has no history, so `collect` promises only that each element is producible;
// Creusot's `x == v` and `cnt == x.len()` are not stated.
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

    // `collect` delegates to `from_iter`, as in `tests/ui/pass/creusot/weaker/decuple_range.rs`.
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

struct Map<I, F> {
    iter: I,
    func: F,
    produced: Ghost<Seq<UInt>>,
}

impl<I: Model, F> Model for Map<I, F> {
    type Ty = (<I as Model>::Ty, Closure<F>, Seq<UInt>);
}

fn push_produced(produced: Ghost<Seq<UInt>>, x: u32) -> Ghost<Seq<UInt>> {
    thrust_macros::ghost!(|produced: Ghost<Seq<UInt>>, x: u32| -> Seq<UInt> { produced.push(x) })
}

#[thrust_macros::context]
impl<I: Iterator<Item = u32> + Model, F: FnMut(u32, Ghost<Seq<UInt>>) -> u32> Iterator for Map<I, F>
where
    <I as Model>::Ty: PartialEq,
{
    type Item = u32;

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
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        I::invariant(self.0)
            && forall(|e: UInt| !I::produces(self.0, e) || thrust_macros::pre!((self.1)(e, self.2)))
            && forall(|h: Seq<UInt>|
                forall(|e1: UInt|
                    forall(|e2: UInt|
                        forall(|b: UInt|
                            forall(|g2: Closure<F>|
                                !(I::produces(self.0, e1)
                                    && I::produces(self.0, e2)
                                    && thrust_macros::pre!((self.1)(e1, h))
                                    && thrust_macros::post!(Mut::new(self.1, g2)(e1, h), b))
                                    || thrust_macros::pre!((g2)(e2, h.push(e1))))))))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        I::completed(Mut::new((*self).0, (!self).0))
            && (*self).1 == (!self).1
            && (*self).2 == (!self).2
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        exists(|i: UInt|
            I::step(self.0, i, dist.0)
                && thrust_macros::pre!((self.1)(i, self.2))
                && thrust_macros::post!(Mut::new(self.1, dist.1)(i, self.2), item)
                && dist.2 == self.2.push(i))
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        exists(|j: UInt|
            exists(|g2: Closure<F>|
                I::produces(self.0, j)
                    && thrust_macros::pre!((self.1)(j, self.2))
                    && thrust_macros::post!(Mut::new(self.1, g2)(j, self.2), item)))
    }
}

#[derive(PartialEq)]
struct Range {
    start: u32,
    end: u32,
}

impl Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = u32;

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

// `FromIterator<A>` reduced to `from_iter` over `&mut I`; the step form of `traits/collect_visited_seq_i64.rs`.
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
impl FromIterator<u32> for Vec<u32> {
    fn from_iter<I: Iterator<Item = u32> + Model>(iter: &mut I) -> Vec<u32>
    where
        <I as Model>::Ty: PartialEq,
    {
        let it = iter;
        let mut v: Vec<u32> = Vec::new();
        while let Some(x) = it.next() {
            thrust_macros::invariant!(
                |it: &mut I, v: Vec<u32>, iter: thrust_models::FnParam<&mut I>|
                !it == !iter.at_entry()
                    && I::invariant(*it)
                    && forall(|e: UInt| I::produces(*it, e) ==> I::produces(*iter.at_entry(), e))
                    && forall(|k: Int| 0 <= k && k < v.len() ==> I::produces(*iter.at_entry(), v[k]))
            );
            v.push(x);
        }
        v
    }
}

// Creusot: `proof_assert! { (@x).ext_eq(@v) }; proof_assert! { @cnt == (@x).len() }`. Here: the
// closure's history-dependent precondition is discharged at every call, and each element is one
// the range produces.
#[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> start <= result[k] && result[k] < end))]
fn counter(start: u32, end: u32) -> Vec<u32> {
    let mut cnt: usize = 0;
    let f = thrust_macros::closure!(
        captures(cnt: &mut &mut usize),
        requires(*(*cnt) == produced.len()),
        ensures(*(!cnt) == *(*cnt) + 1 && result == x),
        |x: u32, produced: Ghost<Seq<UInt>>| -> u32 { cnt += 1; x },
    );
    let mut m = Map {
        iter: Range { start, end },
        func: f,
        produced: thrust_macros::ghost!(|| -> Seq<UInt> { Seq::empty() }),
    };
    m.collect::<Vec<u32>>()
}

fn main() {}
