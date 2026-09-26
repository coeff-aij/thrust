//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3
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

impl<I: thrust_models::Model> thrust_models::Model for Id<I> {
    type Ty = Id<<I as thrust_models::Model>::Ty>;
}

#[thrust_macros::context]
impl<I> Iterator for Id<I>
where
    I: Iterator + thrust_models::Model,
    <I as Iterator>::Item: thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
    <<I as Iterator>::Item as thrust_models::Model>::Ty:
        thrust_models::Model<Ty = <<I as Iterator>::Item as thrust_models::Model>::Ty> + PartialEq,
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
        I::completed(thrust_models::model::Mut::new((*self).iter, (!self).iter))
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.step(item, dist.iter)
        I::step(self.iter, item, dist.iter)
    }

    fn next(&mut self) -> Option<I::Item> {
        self.iter.next()
    }
}

fn main() {}
