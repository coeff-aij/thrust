//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
use thrust_models::{Model, model::Mut};
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

pub struct Id<I> {
    iter: I,
}

impl<I: Model> Model for Id<I> {
    type Ty = Id<<I as Model>::Ty>;
}

#[thrust_macros::context]
impl<I> Iterator for Id<I>
where
    I: Iterator + Model,
    <I as Iterator>::Item: Model,
    <<I as Iterator>::Item as Model>::Ty:
        Model<Ty = <<I as Iterator>::Item as Model>::Ty>,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant()
        I::invariant(self.iter)
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed()
        I::completed(Mut::new((*self).iter, (!self).iter))
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.step(item, dist.iter)
        I::step(self.iter, item, dist.iter)
    }

    fn next(&mut self) -> Option<I::Item> {
        self.iter.next();
        None
    }
}

fn main() {}
