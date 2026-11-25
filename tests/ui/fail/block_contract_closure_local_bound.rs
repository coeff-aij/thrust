//@compile-flags: -C debug-assertions=off
// A type parameter a block contract declares must be met by the closure it stands for, as in
// `assume!`: this one is `FnMut`.
use thrust_models::{Model, model::Closure};
pub struct Wrap<F> {
    n: i64,
    f: F,
}

impl<F> Model for Wrap<F> {
    type Ty = (<i64 as Model>::Ty, Closure<F>);
}

fn run(n: i64) -> i64 {
    let mut calls = 0;
    let w = Wrap { n, f: move |x: i64| { calls += 1; x + calls } };
    let r;
    thrust_macros::block_contract!( //~ ERROR: `P` stands for
        requires(<P: Fn(i64) -> i64> |w: Wrap<P>| true),
        ensures(|r: i64| true),
        {
            r = w.n;
        }
    );
    r
}

fn main() {
    let _ = run(1);
}
