//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::context]
trait A {
    type Item;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::ok(*self, i)))]
    fn get(&mut self) -> Option<Self::Item>;

    fn other(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn ok(self, i: Self::Item) -> bool;
}

struct W<I> {
    inner: I,
}

impl<I: thrust_models::Model> thrust_models::Model for W<I> {
    type Ty = (<I as thrust_models::Model>::Ty,);
}

#[thrust_macros::context]
impl<I> A for W<I>
where
    I: A + thrust_models::Model,
    <I as A>::Item: thrust_models::Model,
    <<I as A>::Item as thrust_models::Model>::Ty: PartialEq,
    <I as thrust_models::Model>::Ty: PartialEq,
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
            None => None,
            _ => self.inner.other(),
        }
    }
}

fn main() {}
