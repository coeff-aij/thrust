//@compile-flags: -C debug-assertions=off
// A declared type parameter must occur in a parameter's type.

pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> thrust_models::Model for Wrap<F> {
    type Ty = (<i64 as thrust_models::Model>::Ty, thrust_models::model::Closure<F>);
}

fn run(n: i64) -> i64 {
    let w = Wrap { n, f: |x: i64| x };
    thrust_macros::assume!(<P: Fn(i64) -> i64> |w: Wrap<_>| true); //~ ERROR: `P` occurs in no parameter's type
    w.n
}

fn main() {
    let _ = run(1);
}
