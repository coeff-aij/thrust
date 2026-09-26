//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3

// The mapper is narrower than the range it is applied to: `1..5` produces `1`,
// which a closure defined only above `1` cannot be called on.
use thrust_models::model::{Closure, Mut, Seq};
use thrust_models::{exists, forall, Model};

#[thrust_macros::context]
trait Iterator
where
    Self::Item: Model,
{
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
    // The produced item as a one-element sequence. The literal's element type is the adapter's
    // `Item` projection, which has to resolve at every instantiation of this contract.
    #[thrust_macros::ensures(forall(|i| forall(|s: Seq<<Self::Item as Model>::Ty>|
        result == Some(i) && s == Seq::singleton(i) ==> s.len() == 1 && s[0] == i)))]
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
}

struct Map<I, F> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,
}

impl<I: thrust_models::Model, F> thrust_models::Model for Map<I, F> {
    type Ty = Map<<I as thrust_models::Model>::Ty, Closure<F>>;
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
        // self.iter.invariant() &&
        // forall(|i: I::Item| self.iter.produces(i) ==> pre!(self.func(i)))
        I::invariant(self.iter)
            && forall(|i: <<I as Iterator>::Item as thrust_models::Model>::Ty|
                !I::produces(self.iter, i) || thrust_macros::pre!((self.func)(i)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: I::Item| self.iter.step(i, dist.iter)
        //     && pre!(self.func(i)) && post!(self.func(i), item))
        // && self.func == dist.func
        exists(|i: <<I as Iterator>::Item as thrust_models::Model>::Ty|
            I::step(self.iter, i, dist.iter)
                && thrust_macros::pre!((self.func)(i))
                && thrust_macros::post!((self.func)(i), item)
                && self.func == dist.func)
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // exists(|j: I::Item| self.iter.produces(j)
        //     && pre!(self.func(j)) && post!(self.func(j), item))
        exists(|j: <<I as Iterator>::Item as thrust_models::Model>::Ty|
            I::produces(self.iter, j)
                && thrust_macros::pre!((self.func)(j))
                && thrust_macros::post!((self.func)(j), item))
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
}

// The call site the guard is for: the mapper is only defined for positive
// arguments, and every item a `1..5` range can produce is positive.
fn main() {
    let f = thrust_macros::closure!(
        requires(x > 1),
        ensures(result == x + 1),
        |x: i64| -> i64 { x + 1 },
    );
    let mut m = Map {
        iter: Range { start: 1, end: 5 },
        func: f,
    };
    let _ = m.next();
}
