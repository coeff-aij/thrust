//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
use thrust_models::Model;
#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self))]
    #[thrust_macros::ensures(Self::p(!self))]
    fn f(&mut self);

    #[thrust_macros::requires(Self::p(*self))]
    fn g(&mut self);

    #[thrust_macros::predicate]
    fn p(self) -> bool;
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
{
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        I::p(self.0)
    }

    fn g(&mut self) {}

    fn f(&mut self) {
        self.inner.g()
    }
}

fn main() {}
