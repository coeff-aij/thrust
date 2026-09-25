//@check-pass
// An adapter's `produces` is existential in substance: an item is what the
// adapter yields for *some* pending element of the inner iterator. Written
// with an SMT `exists`, the monotonicity law over it leaves the caller of
// `next` with nothing -- the whole postcondition stops constraining the
// returned value. Naming the pending element makes the law quantifier-free,
// and the call site can then pin the item down.
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::model::Int;
use thrust_models::{exists, forall};

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
    #[thrust_macros::ensures(forall(|s, i| Self::produces_seeded(!self, s, i) ==> Self::produces_seeded(*self, s, i)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
    /// `item` is among what `self` may still produce.
    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool;
    /// `item` is what `self` still produces from the pending element `seed`.
    #[thrust_macros::predicate]
    fn produces_seeded(self, seed: Self::Item, item: Self::Item) -> bool;
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
        !((*self).start < (*self).end) && *self == !self
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
    fn produces(self, item: Self::Item) -> bool {
        // self.start <= item && item < self.end
        self.start <= item && item < self.end
    }

    #[thrust_macros::predicate]
    fn produces_seeded(self, seed: Self::Item, item: Self::Item) -> bool {
        self.start <= seed && seed < self.end && item == seed
    }
}


#[derive(PartialEq)]
struct Inc {
    iter: Range,
}

impl thrust_models::Model for Inc {
    type Ty = Inc;
}

#[thrust_macros::context]
impl Iterator for Inc {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some(v + 1),
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        !((*self).iter.start < (*self).iter.end) && *self == !self
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        exists(|i: Int|
            self.iter.start < self.iter.end
                && self.iter.end == dist.iter.end
                && self.iter.start == i
                && self.iter.start + 1 == dist.iter.start
                && item == i + 1)
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        exists(|j: Int|
            self.iter.start <= j && j < self.iter.end && item == j + 1)
    }

    #[thrust_macros::predicate]
    fn produces_seeded(self, seed: Self::Item, item: Self::Item) -> bool {
        self.iter.start <= seed && seed < self.iter.end && item == seed + 1
    }
}

fn main() {
    let mut m = Inc { iter: Range { start: 1, end: 5 } };
    let o = m.next();
    match o {
        Some(x) => assert!(x == 2),
        None => {}
    }
}
