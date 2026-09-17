//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest
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

pub struct Fuse<I> {
    iter: Option<I>,
}

impl<I> thrust_models::Model for Fuse<I> {
    type Ty = Fuse<I>;
}

#[thrust_macros::context]
impl<I> Iterator for Fuse<I>
where
    I: Iterator + thrust_models::Model,
    <I as Iterator>::Item: thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.is_none()
        //   or self.iter.is_some()
        // && self.iter.unwrap().invariant()
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // *self.iter.is_none() || *self.iter.is_some() && !self.iter.is_none() && exists(|i: I| Self::completed(Mut::new(*self.iter.unwrap(), i)))
        "true";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.is_some()
        // && dist.iter.is_some()
        // && self.iter.unwrap().step(item, dist.iter.unwrap())
        "true";
        true
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
