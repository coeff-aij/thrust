//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:develop-2493045c3
use thrust_models::model::Mut;
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

pub struct Fuse<I> {
    iter: Option<I>,
}

impl<I: thrust_models::Model> thrust_models::Model for Fuse<I> {
    type Ty = Fuse<<I as thrust_models::Model>::Ty>;
}

#[thrust_macros::context]
impl<I> Iterator for Fuse<I>
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
        // self.iter == None || exists(|i| self.iter == Some(i) && I::invariant(i))
        self.iter == None
            || exists(|i: <I as thrust_models::Model>::Ty| self.iter == Some(i) && I::invariant(i))
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // (*self).iter == None
        //     || (!self).iter == None && exists(|cur, i|
        //         (*self).iter == Some(cur) && I::completed(Mut::new(cur, i)))
        (*self).iter == None
            || ((!self).iter == None
                && exists(|cur: <I as thrust_models::Model>::Ty| exists(|i: <I as thrust_models::Model>::Ty|
                    (*self).iter == Some(cur) && I::completed(Mut::new(cur, i)))))
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // exists(|i, d| self.iter == Some(i) && dist.iter == Some(d)
        //     && I::step(i, item, d))
        exists(|i: <I as thrust_models::Model>::Ty| exists(|d: <I as thrust_models::Model>::Ty|
            self.iter == Some(i) && dist.iter == Some(d) && I::step(i, item, d)))
    }

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            None => None,
            Some(iter) => match iter.next() {
                None => {
                    self.iter = None;
                    None
                }
                x => x,
            },
        }
    }
}

fn main() {}
