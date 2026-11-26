//@compile-flags: -C debug-assertions=off
// One declared type parameter cannot stand for two closures.
use thrust_models::{Model, model::Closure};
pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> Model for Wrap<F> {
    type Ty = (<i64 as Model>::Ty, Closure<F>);
}

fn run(n: i64) -> i64 {
    let v = Wrap { n, f: |x: i64| x + 1 };
    let w = Wrap { n, f: |x: i64| x };
    thrust_macros::assume!(<P: Fn(i64) -> i64> |v: Wrap<P>, w: Wrap<P>| true); //~ ERROR: `P` stands for two closures' types
    w.n
}

fn main() {
    let _ = run(1);
}
