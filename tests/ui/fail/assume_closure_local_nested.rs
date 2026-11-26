//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `_` inside a written type, behind `&mut` in a generic struct (`&mut Wrap<_>`), stands for the
// closure type at that position of the local's type. The assumed `n >= 0` does not give the closure's
// precondition at `n`, which `call` requires, at 0.
use thrust_models::{Model, model::Closure};
pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> Model for Wrap<F> {
    type Ty = (<i64 as Model>::Ty, Closure<F>);
}

#[thrust_macros::context]
impl<F: Fn(i64) -> i64> Wrap<F> {
    #[thrust_macros::predicate]
    fn callable(f: F, n: i64) -> bool {
        thrust_macros::pre!(f(n))
    }

    #[thrust_macros::requires(Self::callable((*self).1, (*self).0))]
    #[thrust_macros::ensures(true)]
    fn call(&mut self) -> i64 {
        (self.f)(self.n)
    }
}

#[thrust_macros::requires(true)]
fn run(n: i64) -> i64 {
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result == x),
        |x: i64| -> i64 { x },
    );
    let mut w = Wrap { n, f };
    let r = &mut w;
    thrust_macros::assume!(|r: &mut Wrap<_>| (*r).0 >= 0);
    r.call()
}

fn main() {
    let _ = run(1);
}
