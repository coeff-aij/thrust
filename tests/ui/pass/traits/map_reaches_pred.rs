//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::model::{Closure, Int, Mut};
use thrust_models::{exists, forall};

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
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // !(*self.start < *self.end) && *self == !self
        !((*self).start < (*self).end)
            && (*self).start == (!self).start
            && (*self).end == (!self).end
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.start < self.end && self.end == dist.end && self.start == item
        // && self.start + 1 == dist.start
        self.start < self.end
            && self.end == dist.end
            && self.start == item
            && self.start + 1 == dist.start
    }

    #[thrust_macros::predicate]
    fn reaches(self, dist: Self) -> bool {
        // self.start <= dist.start && self.end == dist.end
        self.start <= dist.start && self.end == dist.end
    }
}

struct Map<F> {
    iter: Range,
    func: F,
}

impl<F> thrust_models::Model for Map<F> {
    type Ty = Map<Closure<F>>;
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
        Range::invariant(self.iter)
            && forall(|m: Range|
                forall(|e: Int|
                    forall(|n: Range|
                        !(Range::reaches(self.iter, m) && Range::step(m, e, n))
                            || thrust_macros::pre!((self.func)(e)))))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        Range::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: i64| self.iter.step(i, dist.iter)) &&
        // pre!(self.func(i)) && post!(self.func(i), item) && self.func == dist.func
        exists(|i: Int|
            Range::step(self.iter, i, dist.iter)
                && thrust_macros::pre!((self.func)(i))
                && thrust_macros::post!((self.func)(i), item)
                && self.func == dist.func)
    }

    #[thrust_macros::predicate]
    fn reaches(self, dist: Self) -> bool {
        // self.iter.reaches(dist.iter) && self.func == dist.func
        Range::reaches(self.iter, dist.iter) && self.func == dist.func
    }
}

fn main() {}
