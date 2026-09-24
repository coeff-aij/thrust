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
    #[thrust_macros::ensures(Self::reaches(*self, !self))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
    /// Reflexive-transitive closure of `step`, with the produced items forgotten.
    #[thrust_macros::predicate]
    fn reaches(self, dist: Self) -> bool;
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

    #[thrust_macros::predicate]
    fn reaches(self, dist: Self) -> bool {
        // Reflexivity broken: a range no longer reaches itself, so the state that
        // produces the very next item is not among the reachable ones and the
        // mapper's precondition goes undischarged there.
        // self.start < dist.start && self.end == dist.end
        "(and
            (< (tuple_proj<Int-Int>.0 self_) (tuple_proj<Int-Int>.0 dist))
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 dist))
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
        // forall(|m: Range, e: i64, m2: Range|
        //     self.iter.reaches(m) && m.step(e, m2) ==> pre!(self.func(e)))
        //
        // The guard is the composition the generic form would state with a trait
        // predicate: an item is demanded of the mapper only when some state the
        // inner iterator can reach steps to it. `Range`'s `reaches` and `step` are
        // concrete here, so both are `define-fun`s rather than forall-predicates.
        //
        // The intermediate states are bound field by field: a binder whose sort is
        // a packed tuple is what crashes the solver's parser.
        "(and
            (p_invariant_e2b28941db239feabeba1f7363d369b6 (tuple_proj<Tuple<Int-Int>-a0>.0 self_))
            (forall ((m0 Int) (m1 Int) (e Int) (n0 Int) (n1 Int))
                (=>
                    (and
                        (p_reaches_e2b28941db239fea5912d328a9ab0865 (tuple_proj<Tuple<Int-Int>-a0>.0 self_) (tuple<Int-Int> m0 m1))
                        (p_step_e2b28941db239fea3bd4c0e9329eae09 (tuple<Int-Int> m0 m1) e (tuple<Int-Int> n0 n1))
                    )
                    (q_pre_next_e2b28941db239fea9a2b32390d18b1c8<a0> (tuple_proj<Tuple<Int-Int>-a0>.1 self_) e)
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        "(and
            (p_completed_e2b28941db239fea26aab556cc20ae95
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
                (p_step_e2b28941db239fea3bd4c0e9329eae09
                    (tuple_proj<Tuple<Int-Int>-a0>.0 self_)
                    i
                    (tuple_proj<Tuple<Int-Int>-a0>.0 dist)
                )
                (q_pre_next_e2b28941db239fea9a2b32390d18b1c8<a0> (tuple_proj<Tuple<Int-Int>-a0>.1 self_) i)
                (q_post_next_e2b28941db239fea9a2b32390d18b1c8<a0> (tuple_proj<Tuple<Int-Int>-a0>.1 self_) i item)
                (=
                    (tuple_proj<Tuple<Int-Int>-a0>.1 self_)
                    (tuple_proj<Tuple<Int-Int>-a0>.1 dist)
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn reaches(self, dist: Self) -> bool {
        // self.iter.reaches(dist.iter) && self.func == dist.func
        "(and
            (p_reaches_e2b28941db239fea5912d328a9ab0865 (tuple_proj<Tuple<Int-Int>-a0>.0 self_) (tuple_proj<Tuple<Int-Int>-a0>.0 dist))
            (= (tuple_proj<Tuple<Int-Int>-a0>.1 self_) (tuple_proj<Tuple<Int-Int>-a0>.1 dist))
        )";
        true
    }
}

fn main() {}
