//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3
use thrust_models::model::{Closure, Mut};
use thrust_models::{exists, forall};

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
                None
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() &&
        // forall(|i: I::Item, dist: I| self.iter.step(i, dist) ==> pre!(self.func(i)))
        I::invariant(self.iter)
            && forall(|i: <<I as Iterator>::Item as thrust_models::Model>::Ty|
                forall(|dist: <I as thrust_models::Model>::Ty|
                    !I::step(self.iter, i, dist)
                        || thrust_macros::pre!((self.func)(i))))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i: Self::Item| self.iter.step(i, dist.iter)) &&
        // pre!(self.func(i)) && post!(self.func(i), item)
        exists(|i: <<I as Iterator>::Item as thrust_models::Model>::Ty|
            I::step(self.iter, i, dist.iter)
                && thrust_macros::pre!((self.func)(i))
                && thrust_macros::post!((self.func)(i), item)
                && self.func == dist.func)
    }
}

fn main() {}
