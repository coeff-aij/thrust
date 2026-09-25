//@error-in-other-file: Unsat
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
    #[thrust_macros::ensures(forall(|i| Self::produces(!self, i) ==> Self::produces(*self, i)))]
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
    iter: I,
    func: F,
}

impl<I: thrust_models::Model, F> thrust_models::Model for Map<I, F> {
    type Ty = Map<<I as thrust_models::Model>::Ty, Closure<F>>;
}

#[thrust_macros::context]
impl<I: Iterator<Item = i64> + thrust_models::Model, F: Fn(i64) -> i64> Iterator for Map<I, F>
where
    <I as thrust_models::Model>::Ty: PartialEq,
{
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
        // forall(|e: i64| self.iter.produces(e) ==> pre!(self.func(e)))
        //
        // The guard is unary: the mapper's precondition is demanded only of items
        // the inner iterator may still produce. No iterator state is bound, which
        // is what keeps the call-site discharge tractable.
        I::invariant(self.iter)
            && forall(|ze: Int|
                !I::produces(self.iter, ze) || thrust_macros::pre!((self.func)(ze)))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: i64| self.iter.step(i, dist.iter)
        //     && pre!(self.func(i)) && post!(self.func(i), item))
        // && self.func == dist.func
        exists(|zi: Int|
            I::step(self.iter, zi, dist.iter)
                && thrust_macros::pre!((self.func)(zi))
                && thrust_macros::post!((self.func)(zi), item)
                && self.func == dist.func)
    }

    #[thrust_macros::predicate]
    fn produces(self, item: Self::Item) -> bool {
        // exists(|j: i64| self.iter.produces(j)
        //     && pre!(self.func(j)) && post!(self.func(j), item))
        exists(|zj: Int|
            I::produces(self.iter, zj)
                && thrust_macros::pre!((self.func)(zj))
                && thrust_macros::post!((self.func)(zj), item))
    }
}

fn main() {}
