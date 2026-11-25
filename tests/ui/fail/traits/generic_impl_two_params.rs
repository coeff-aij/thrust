//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
use thrust_models::{Model, model::Closure};
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

impl<I: Model, F> Model for M<I, F> {
    type Ty = (<I as Model>::Ty, Closure<F>);
}

#[thrust_macros::context]
impl<I, F> A for M<I, F>
where
    I: A + Model,
    F: FnMut(i64) -> i64,
{
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        I::p(self.0)
    }

    fn g(&mut self) {}

    fn f(&mut self) {
        self.iter.g()
    }
}

fn main() {}
