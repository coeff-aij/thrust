//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-3d34b93de
use thrust_models::forall;
use thrust_models::model::{Closure, Int, Seq};
use thrust_models::{Ghost, Model};

// Creusot's `examples/counter`: `v.iter().map_inv(|x, _prod| { cnt += 1; *x }).collect()`, where
// the closure's precondition `cnt == _prod.len()` reads the history. The iterator spec is the
// step form with a unary `produces1` guard; `Map` carries Creusot's `MapInv` ghost `produced`
// and takes an `FnMut(i64, Ghost<Seq<Int>>)`. The source is a `Range` instead of `v.iter()`.
//
// The step form has no history, so `collect` promises only that each element is producible;
// Creusot's `x == v` and `cnt == x.len()` are not stated.
#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::produces1(*self, i)))]
    #[thrust_macros::ensures(forall(|i| Self::produces1(!self, i) ==> Self::produces1(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;

    // `collect` delegates to `from_iter`, as in `tests/ui/pass/examples/decuple_range.rs`.
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
    #[thrust_macros::predicate]
    fn produces1(self, item: Self::Item) -> bool;
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
impl<I: Iterator<Item = i64> + Model, F: FnMut(i64, Ghost<Seq<Int>>) -> i64> Iterator for Map<I, F>
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
    // && forall(|e| self.iter.produces1(e) ==> pre!(self.func(e, self.produced)))
    // && forall(|h, e1, e2, b| self.iter.produces1(e1) && self.iter.produces1(e2)
    //        && pre!(self.func(e1, h)) && post!(self.func(e1, h), b) ==> pre!(self.func(e2, h.push(e1))))
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "(and (q_invariant_70773323ab54f8f52546ff7eb9bf2990<a0> (tuple_proj<a0-a1-Seq<Int>>.0 self_)) (forall ((e Int)) (=> (q_produces1_70773323ab54f8f5ebeed520b2c74355<a0> (tuple_proj<a0-a1-Seq<Int>>.0 self_) e) (q_pre_next_70773323ab54f8f5e0f0df431c6ab55<a1> (tuple_proj<a0-a1-Seq<Int>>.1 self_) e (tuple_proj<a0-a1-Seq<Int>>.2 self_)))) (forall ((harr (Seq Int)) (e1 Int) (e2 Int) (b Int) (g a1) (g2 a1))
            (=> (and (q_produces1_70773323ab54f8f5ebeed520b2c74355<a0> (tuple_proj<a0-a1-Seq<Int>>.0 self_) e1) (q_produces1_70773323ab54f8f5ebeed520b2c74355<a0> (tuple_proj<a0-a1-Seq<Int>>.0 self_) e2)
                     (q_pre_next_70773323ab54f8f5e0f0df431c6ab55<a1> g e1 harr)
                     (q_post_next_70773323ab54f8f5e0f0df431c6ab55<a1> (mut<a1> g g2) e1 harr b))
                (q_pre_next_70773323ab54f8f5e0f0df431c6ab55<a1> g2 e2 (seq.++ harr (seq.unit e1))))))";
        true
    }

    // self.iter.completed() && *self.func == !self.func && *self.produced == !self.produced
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(and (q_completed_70773323ab54f8f530f1c291ef06cef3<a0> (mut<a0> (tuple_proj<a0-a1-Seq<Int>>.0 (mut_current<Tuple<a0-a1-Seq<Int>>> self_)) (tuple_proj<a0-a1-Seq<Int>>.0 (mut_final<Tuple<a0-a1-Seq<Int>>> self_))))
            (= (tuple_proj<a0-a1-Seq<Int>>.1 (mut_current<Tuple<a0-a1-Seq<Int>>> self_)) (tuple_proj<a0-a1-Seq<Int>>.1 (mut_final<Tuple<a0-a1-Seq<Int>>> self_)))
            (= (tuple_proj<a0-a1-Seq<Int>>.2 (mut_current<Tuple<a0-a1-Seq<Int>>> self_)) (tuple_proj<a0-a1-Seq<Int>>.2 (mut_final<Tuple<a0-a1-Seq<Int>>> self_))))";
        true
    }

    // exists(|i| self.iter.step(i, dist.iter) && pre!(self.func(i, self.produced))
    //    && post!(self.func(i, self.produced), item) && self.func == dist.func
    //    && dist.produced == self.produced.push(i))
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        "(exists ((i Int))
        (and (q_step_70773323ab54f8f5ad42ca680bcd726f<a0> (tuple_proj<a0-a1-Seq<Int>>.0 self_) i (tuple_proj<a0-a1-Seq<Int>>.0 dist))
             (q_pre_next_70773323ab54f8f5e0f0df431c6ab55<a1> (tuple_proj<a0-a1-Seq<Int>>.1 self_) i (tuple_proj<a0-a1-Seq<Int>>.2 self_))
             (q_post_next_70773323ab54f8f5e0f0df431c6ab55<a1> (mut<a1> (tuple_proj<a0-a1-Seq<Int>>.1 self_) (tuple_proj<a0-a1-Seq<Int>>.1 dist)) i (tuple_proj<a0-a1-Seq<Int>>.2 self_) item)
             (= (tuple_proj<a0-a1-Seq<Int>>.2 dist) (seq.++ (tuple_proj<a0-a1-Seq<Int>>.2 self_) (seq.unit i)))))";
        true
    }

    // exists(|j| self.iter.produces1(j) && pre!(self.func(j, self.produced)) && post!(self.func(j, self.produced), item))
    #[thrust_macros::predicate]
    fn produces1(self, item: Self::Item) -> bool {
        "(exists ((j Int) (harr (Seq Int)) (g a1) (g2 a1))
        (and (q_produces1_70773323ab54f8f5ebeed520b2c74355<a0> (tuple_proj<a0-a1-Seq<Int>>.0 self_) j) (q_pre_next_70773323ab54f8f5e0f0df431c6ab55<a1> g j harr) (q_post_next_70773323ab54f8f5e0f0df431c6ab55<a1> (mut<a1> g g2) j harr item)))";
        true
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
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        "(and
            (not (< (tuple_proj<Int-Int>.0 (mut_current<Tuple<Int-Int>> self_)) (tuple_proj<Int-Int>.1 (mut_current<Tuple<Int-Int>> self_))))
            (= (mut_current<Tuple<Int-Int>> self_) (mut_final<Tuple<Int-Int>> self_)))";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        "(and
            (< (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.1 self_))
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self_) item)
            (= (+ (tuple_proj<Int-Int>.0 self_) 1) (tuple_proj<Int-Int>.0 dist)))";
        true
    }

    #[thrust_macros::predicate]
    fn produces1(self, item: Self::Item) -> bool {
        "(and (<= (tuple_proj<Int-Int>.0 self_) item) (< item (tuple_proj<Int-Int>.1 self_)))";
        true
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

// Creusot: `proof_assert! { (@x).ext_eq(@v) }; proof_assert! { @cnt == (@x).len() }`. Here: the
// closure's history-dependent precondition is discharged at every call, and each element is one
// the range produces. Unsat: the first element is `start`.
#[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < result.len() ==> start < result[k] && result[k] < end))]
fn counter(start: i64, end: i64) -> Vec<i64> {
    let mut cnt: i64 = 0;
    let f = thrust_macros::closure!(
        captures(cnt: &mut &mut i64),
        requires(*(*cnt) == produced.len()),
        ensures(*(!cnt) == *(*cnt) + 1 && result == x),
        |x: i64, produced: Ghost<Seq<Int>>| -> i64 { cnt += 1; x },
    );
    let mut m = Map {
        iter: Range { start, end },
        func: f,
        produced: thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }),
    };
    m.collect::<Vec<i64>>()
}

fn main() {}
