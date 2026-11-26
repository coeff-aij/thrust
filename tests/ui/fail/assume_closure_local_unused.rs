//@compile-flags: -C debug-assertions=off
// A declared type parameter must occur in a parameter's type.
use thrust_models::{Model, model::Closure};
pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> Model for Wrap<F> {
    type Ty = (<i64 as Model>::Ty, Closure<F>);
}

fn run(n: i64) -> i64 {
    let w = Wrap { n, f: |x: i64| x };
    thrust_macros::assume!(<P: Fn(i64) -> i64> |w: Wrap<_>| true); //~ ERROR: `P` occurs in no parameter's type
    w.n
}

fn main() {
    let _ = run(1);
}
