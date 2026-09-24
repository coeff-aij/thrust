//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest
use thrust_models::forall;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}

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
}

struct Map<F> {
    iter: Range,
    func: F,
}

impl<F> thrust_models::Model for Map<F> {
    type Ty = Map<F>;
}

#[thrust_macros::context]
impl<F: Fn(i64) -> i64> Iterator for Map<F> {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() &&
        // forall(|e: i64| self.iter.start <= e && e < self.iter.end ==> pre!(self.func(e)))
        //
        // Narrowed to a strict `<`, so the item the inner iterator produces next --
        // which is `start` itself -- is the one item left outside the guard, and the
        // call to the mapper can no longer discharge its precondition.
        //
        // The second conjunct is the point of this test: the closure's precondition
        // is demanded only of the items the inner iterator can still produce, not of
        // every `i64` as in `map_fn_uncond_pre.rs`. `start <= e < end` is what
        // `reaches`-then-`step` amounts to once the inner iterator is a concrete
        // `Range`, so every bound variable here ranges over `Int`.
        "(and
            (p_invariant_d12f2014f51a8bc8a3aed88fdc0f9a69 (tuple_proj<Tuple<Int-Int>-a0>.0 self_))
            (forall ((e Int))
                (=>
                    (and
                        (< (tuple_proj<Int-Int>.0 (tuple_proj<Tuple<Int-Int>-a0>.0 self_)) e)
                        (< e (tuple_proj<Int-Int>.1 (tuple_proj<Tuple<Int-Int>-a0>.0 self_)))
                    )
                    (q_pre_next_d12f2014f51a8bc8febe2115a8ed8d4<a0> (tuple_proj<Tuple<Int-Int>-a0>.1 self_) e)
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        "(and
            (p_completed_d12f2014f51a8bc889c6dffa4912403c
                (mut<Tuple<Int-Int>>
                    (tuple_proj<Tuple<Int-Int>-a0>.0 (mut_current<Tuple<Tuple<Int-Int>-a0>> self_))
                    (tuple_proj<Tuple<Int-Int>-a0>.0 (mut_final<Tuple<Tuple<Int-Int>-a0>> self_))
                )
            )
            (=
                (tuple_proj<Tuple<Int-Int>-a0>.1 (mut_current<Tuple<Tuple<Int-Int>-a0>> self_))
                (tuple_proj<Tuple<Int-Int>-a0>.1 (mut_final<Tuple<Tuple<Int-Int>-a0>> self_))
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: i64| self.iter.step(i, dist.iter)) &&
        // pre!(self.func(i)) && post!(self.func(i), item) && self.func == dist.func
        "(exists ((i Int))
            (and
                (p_step_d12f2014f51a8bc81dfee9c4de95a226
                    (tuple_proj<Tuple<Int-Int>-a0>.0 self_)
                    i
                    (tuple_proj<Tuple<Int-Int>-a0>.0 dist)
                )
                (q_pre_next_d12f2014f51a8bc8febe2115a8ed8d4<a0> (tuple_proj<Tuple<Int-Int>-a0>.1 self_) i)
                (q_post_next_d12f2014f51a8bc8febe2115a8ed8d4<a0> (tuple_proj<Tuple<Int-Int>-a0>.1 self_) i item)
                (=
                    (tuple_proj<Tuple<Int-Int>-a0>.1 self_)
                    (tuple_proj<Tuple<Int-Int>-a0>.1 dist)
                )
            )
        )";
        true
    }
}

fn main() {}
