//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `h` requires the `inv` of `a` and takes `b` at a parameter without the bound. `main` builds two
// `Map`s of the same closure type; std.rs's `map` states the closure's `pre!` of the items its
// iterator yields, which the closure of `b`, built with `c = 0`, rejects.
use thrust_models::Model;
#[thrust::trusted]
#[thrust::callable]
fn h<I: IteratorSpec<Item = i64>, J: Iterator<Item = i64>>(a: I, b: J)
where
    I::Item: Model,
{
    let _ = a.count();
    let _ = b.count();
}

fn main() {
    let f = |c: i64| move |x: i64| -> i64 { assert!(x < c); x };
    h((0..3).map(f(10)), (0..3).map(f(0)));
}
