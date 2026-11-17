//@compile-flags: -C debug-assertions=off
// A written type with a `_` must have the shape of the local's type; `w` is not a pair.

pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> thrust_models::Model for Wrap<F> {
    type Ty = (<i64 as thrust_models::Model>::Ty, thrust_models::model::Closure<F>);
}

fn run(n: i64) -> i64 {
    let w = Wrap { n, f: |x: i64| x };
    thrust_macros::assume!(|w: (i64, _)| true); //~ ERROR: in the type of `w`: the written type does not have the shape of `Wrap<
    w.n
}

fn main() {
    let _ = run(1);
}
