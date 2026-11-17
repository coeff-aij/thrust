//@compile-flags: -C debug-assertions=off
// One declared type parameter cannot stand for two closures.

pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> thrust_models::Model for Wrap<F> {
    type Ty = (<i64 as thrust_models::Model>::Ty, thrust_models::model::Closure<F>);
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
