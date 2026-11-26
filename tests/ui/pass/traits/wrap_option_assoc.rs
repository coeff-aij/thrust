//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
use thrust_models::{forall, Model};
#[thrust_macros::context]
trait A {
    type Item;

    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::ok(*self, i)))]
    fn get(&mut self) -> Option<Self::Item>;

    fn other(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn ok(self, i: Self::Item) -> bool;
}

struct W<I> {
    inner: I,
}

impl<I: Model> Model for W<I> {
    type Ty = (<I as Model>::Ty,);
}

#[thrust_macros::context]
impl<I> A for W<I>
where
    I: A + Model,
    <I as A>::Item: Model,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn ok(self, i: Self::Item) -> bool {
        I::ok(self.0, i)
    }

    fn other(&mut self) -> Option<Self::Item> {
        self.inner.other()
    }

    fn get(&mut self) -> Option<Self::Item> {
        match self.inner.get() {
            Some(v) => Some(v),
            None => None,
        }
    }
}

fn main() {}
