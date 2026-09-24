//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120 COAR_IMAGE=coar:develop-2493045c3

// Creusot's `examples/decuple_range`: `(0..10).map(|x| x * 10).collect()` with a closure that is
// defined only below 100. The iterator spec is the step form of `traits/map_call.rs`; `Map` is
// the generic adapter from there, used at `Map<Range, closure>`. Creusot uses `map_inv`; the
// closure here does not read the history, so this is plain `map`.
//
// The step form has no history, so what `collect` can promise is that every collected item is
// one the iterator could produce, not its position: the property checked is the range of each
// element, not Creusot's `v[i] == 10 * i` (`drafts/creusot-examples/decuple_range_visited.rs` states that one).
use thrust_models::forall;
use thrust_models::model::{Closure, Int, Seq};
use thrust_models::Model;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    // `step` relates one call of `next` to its successor state, so an invariant
    // guarded by it ("closure pre for what the inner can step to NOW") is not
    // preserved by `next`. `produces` is monotone under `next`, which is what makes
    // the guard inductive.
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

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
    /// `item` is among what `self` may still produce.
    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool;
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
where <I as thrust_models::Model>::Ty: PartialEq
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
        // self.iter.invariant() &&
        // forall(|i: I::Item| self.iter.produces(i) ==> pre!(self.func(i)))
        "(and
            (q_invariant_535b65d6c851059a677a5e46c08a789<a0> (tuple_proj<a0-a1>.0 self_))
            (forall ((i a7))
                (=>
                    (q_produces_535b65d6c851059ae4cb460e863daa8c<a0>
                        (tuple_proj<a0-a1>.0 self_)
                        i
                    )
                    (q_pre_F_535b65d6c851059ad5d0a5796474cec<a1>
                        (tuple_proj<a0-a1>.1 self_)
                        i
                    )
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        "(and
            (q_completed_535b65d6c851059ae9a463aaf40b8ea0<a0>
                (mut<a0>
                    (tuple_proj<a0-a1>.0 (mut_current<Tuple<a0-a1>> self_))
                    (tuple_proj<a0-a1>.0 (mut_final<Tuple<a0-a1>> self_))
                )
            )
            (=
                (tuple_proj<a0-a1>.1 (mut_current<Tuple<a0-a1>> self_))
                (tuple_proj<a0-a1>.1 (mut_final<Tuple<a0-a1>> self_))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: I::Item| self.iter.step(i, dist.iter)
        //     && pre!(self.func(i)) && post!(self.func(i), item))
        // && self.func == dist.func
        "(exists ((i a7))
            (and
                (q_step_535b65d6c851059abc1b6209b963f472<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    i
                    (tuple_proj<a0-a1>.0 dist)
                )
                (q_pre_F_535b65d6c851059ad5d0a5796474cec<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                )
                (q_post_F_535b65d6c851059ad5d0a5796474cec<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    i
                    item
                )
                (= (tuple_proj<a0-a1>.1 self_) (tuple_proj<a0-a1>.1 dist))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // exists(|j: I::Item| self.iter.produces(j)
        //     && pre!(self.func(j)) && post!(self.func(j), item))
        "(exists ((j a7))
            (and
                (q_produces_535b65d6c851059ae4cb460e863daa8c<a0>
                    (tuple_proj<a0-a1>.0 self_)
                    j
                )
                (q_pre_F_535b65d6c851059ad5d0a5796474cec<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    j
                )
                (q_post_F_535b65d6c851059ad5d0a5796474cec<a1>
                    (tuple_proj<a0-a1>.1 self_)
                    j
                    item
                )
            )
        )";
        true
    }
}

#[derive(PartialEq)]
struct Range {
    start: i64,
    end: i64,
}

impl thrust_models::Model for Range {
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
        // !(*self.start < *self.end) && *self == !self
        "(and
            (not (<
                (tuple_proj<Int-Int>.0 (mut_current<Tuple<Int-Int>> self_))
                (tuple_proj<Int-Int>.1 (mut_current<Tuple<Int-Int>> self_))
            ))
            (= (mut_current<Tuple<Int-Int>> self_) (mut_final<Tuple<Int-Int>> self_))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.start < self.end && self.end == dist.end && self.start == item
        // && self.start + 1 == dist.start
        "(and
            (< (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.1 self_))
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self_) item)
            (= (+ (tuple_proj<Int-Int>.0 self_) 1) (tuple_proj<Int-Int>.0 dist))
        )";
        true
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // self.start <= item && item < self.end
        "(and
            (<= (tuple_proj<Int-Int>.0 self_) item)
            (< item (tuple_proj<Int-Int>.1 self_))
        )";
        true
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
fn decuple_range() -> Vec<i64> {
    let f = thrust_macros::closure!(
        requires(x < 100),
        ensures(result == x * 10),
        |x: i64| -> i64 { x * 10 },
    );
    let mut m = Map {
        iter: Range { start: 0, end: 10 },
        func: f,
    };
    m.collect::<Vec<i64>>()
}

fn main() {}
