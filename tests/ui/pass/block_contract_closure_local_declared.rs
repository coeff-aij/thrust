//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A block contract declares a type parameter before its closure (`<P: Fn(i64) -> i64>`), as
// `assume!` does; its bound lets the formula use `Wrap<P>`'s predicate. The code under the contract
// starts from `requires` alone, whose `callable` of `w`'s own closure is what `call`
// requires.
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
    fn call(&self) -> i64 {
        (self.f)(self.n)
    }
}

#[thrust_macros::requires(n > 0)]
fn run(n: i64) -> i64 {
    let f = thrust_macros::closure!(
        requires(x > 0),
        ensures(result == x),
        |x: i64| -> i64 { x },
    );
    let g = thrust_macros::closure!(
        requires(true),
        ensures(result == x),
        |x: i64| -> i64 { x },
    );
    let w = Wrap { n, f };
    let r;
    thrust_macros::block_contract!(
        requires(<P: Fn(i64) -> i64> |w: Wrap<P>, g: _| Wrap::<P>::callable(w.1, w.0)),
        ensures(<P: Fn(i64) -> i64> |w: Wrap<P>| Wrap::<P>::callable(w.1, w.0)),
        {
            r = w.call() + g(0);
        }
    );
    r
}

fn main() {
    let _ = run(1);
}
