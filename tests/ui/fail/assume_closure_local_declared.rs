//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A type parameter declared before the closure (`<P: Fn(i64) -> i64>`) is left to the local whose
// written type names it, as a `_` is; the formula names it, and its bound lets the formula use
// `Wrap<P>`'s predicate, which requires one. Assumed of another closure, `g`,
// `callable` does not give what `call` requires of `w`'s.
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
    let g = thrust_macros::closure!(
        requires(true),
        ensures(result == x),
        |x: i64| -> i64 { x },
    );
    let mut w = Wrap { n, f };
    thrust_macros::assume!(<P: Fn(i64) -> i64> |w: Wrap<_>, g: P| Wrap::<P>::callable(g, w.0));
    let _ = g(n);
    w.call()
}

fn main() {
    let _ = run(1);
}
