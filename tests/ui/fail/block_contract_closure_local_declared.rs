//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A block contract declares a type parameter before its closure (`<P: Fn(i64) -> i64>`), as
// `assume!` does; its bound lets the formula use `Wrap<P>`'s predicate. The code under the contract
// starts from `block_requires!` alone; stated of another closure, `g`, its `callable` does not
// give what `call` requires of `w`'s.

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
    thrust_macros::block_requires!(
        <P: Fn(i64) -> i64> |w: Wrap<_>, g: P| Wrap::<P>::callable(g, w.0)
    );
    r = w.call() + g(0);
    thrust_macros::block_ensures!(<P: Fn(i64) -> i64> |w: Wrap<P>| Wrap::<P>::callable(w.1, w.0));
    r
}

fn main() {
    let _ = run(1);
}
