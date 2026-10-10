//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

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

struct M<I, F> {
    iter: I,
    func: F,
}

impl<I: thrust_models::Model, F> thrust_models::Model for M<I, F> {
    type Ty = (<I as thrust_models::Model>::Ty, thrust_models::model::Closure<F>);
}

#[thrust_macros::context]
impl<I, F> A for M<I, F>
where
    I: A + thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
    F: FnMut(i64) -> i64,
{
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        I::p(self.0)
    }

    fn g(&mut self) {}

    fn f(&mut self) {
        self.iter.f()
    }
}

fn main() {}
