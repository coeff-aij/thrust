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
impl<I: Iterator + thrust_models::Model, B: thrust_models::Model, F: FnMut(I::Item) -> B> Iterator for Map<I, F>
where
    <B as thrust_models::Model>::Ty: PartialEq,
    I: Iterator + thrust_models::Model,
    <I as Iterator>::Item: thrust_models::Model,
    <<I as Iterator>::Item as thrust_models::Model>::Ty:
        thrust_models::Model<Ty = <<I as Iterator>::Item as thrust_models::Model>::Ty> + PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = <I as Iterator>::Item;
    
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                Some(v)
            }
            None => None,
        }
    }

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant() && (
        //     exists(|dist: I| I::completed(Mut::new(self.iter, dist))) ||
        //     (exists(|i: Self::Item| exists(|dist: I|
        //         self.iter.step(i, dist)
        //     )) && 
        //     forall(|i: Self::Item| forall(|dist: I|
        //         self.iter.step(i, dist) ==>
        //         exists(|f: F| call_pre!(Mut::new(self.func, f)(i)))
        //     )))
        // )
        I::invariant(self.iter)
            && (exists(|dist: <I as thrust_models::Model>::Ty|
                    I::completed(Mut::new(self.iter, dist)))
                || (exists(|i: <<I as Iterator>::Item as thrust_models::Model>::Ty|
                        exists(|dist: <I as thrust_models::Model>::Ty|
                            I::step(self.iter, i, dist)))
                    && forall(|i: <<I as Iterator>::Item as thrust_models::Model>::Ty|
                        forall(|dist: <I as thrust_models::Model>::Ty|
                            !I::step(self.iter, i, dist)
                                || exists(|f: Closure<F>|
                                    thrust_macros::pre!((f)(i)))))))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed() && *self.func == !self.func
        I::completed(Mut::new((*self).iter, (!self).iter)) && (*self).func == (!self).func
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.step(item, dist.iter) && self.func == dist.func
        I::step(self.iter, item, dist.iter) && self.func == self.func
    }
}

fn main() {}
