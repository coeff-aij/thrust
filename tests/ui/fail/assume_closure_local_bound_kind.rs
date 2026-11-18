//@compile-flags: -C debug-assertions=off
// A declared type parameter must be met by the closure it stands for: this one is `FnMut`.

pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> thrust_models::Model for Wrap<F> {
    type Ty = (<i64 as thrust_models::Model>::Ty, thrust_models::model::Closure<F>);
}

fn run(n: i64) -> i64 {
    let mut calls = 0;
    let w = Wrap { n, f: move |x: i64| { calls += 1; x + calls } };
    thrust_macros::assume!(<P: Fn(i64) -> i64> |w: Wrap<P>| true); //~ ERROR: `P` stands for
    w.n
}

fn main() {
    let _ = run(1);
}
