//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A type parameter declared before the closure (`<P: Fn(i64) -> i64>`) is left to the local whose
// written type names it, as a `_` is; the formula names it, and its bound lets the formula use
// `Wrap<P>`'s predicate, which requires one. The assumed `callable` of `w`'s own closure is what
// `call` requires.

pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> thrust_models::Model for Wrap<F> {
    type Ty = (<i64 as thrust_models::Model>::Ty, thrust_models::model::Closure<F>);
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
    thrust_macros::assume!(<P: Fn(i64) -> i64> |w: Wrap<P>, g: _| Wrap::<P>::callable(w.1, w.0));
    let _ = g(n);
    w.call()
}

fn main() {
    let _ = run(1);
}
