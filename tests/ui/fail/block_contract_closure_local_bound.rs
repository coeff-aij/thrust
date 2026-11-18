//@compile-flags: -C debug-assertions=off
// A type parameter a block contract declares must be met by the closure it stands for, as in
// `assume!`: this one is `FnMut`.

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
    let r;
    thrust_macros::block_requires!(<P: Fn(i64) -> i64> |w: Wrap<P>| true); //~ ERROR: `P` stands for
    r = w.n;
    thrust_macros::block_ensures!(|r: i64| true);
    r
}

fn main() {
    let _ = run(1);
}
