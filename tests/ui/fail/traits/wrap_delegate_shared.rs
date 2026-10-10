//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self, x))]
    #[thrust_macros::ensures(Self::p(*self, result))]
    fn f(&self, x: i64) -> i64;

    #[thrust_macros::requires(Self::p(*self, x))]
    fn g(&self, x: i64) -> i64;

    #[thrust_macros::predicate]
    fn p(self, x: i64) -> bool;
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
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn p(self, x: i64) -> bool {
        I::p(self.0, x)
    }

    fn g(&self, x: i64) -> i64 {
        x
    }

    fn f(&self, x: i64) -> i64 {
        self.inner.g(x)
    }
}

fn main() {}
