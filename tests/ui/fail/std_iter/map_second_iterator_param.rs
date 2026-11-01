//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `h` requires the `inv` of `a`, whose `IteratorSpec` states the `pre!` of the closure `a`'s `Map`
// holds, and takes `b` at a parameter without the bound. `main` passes two `Map`s of the same
// closure type, so the closure `b` holds is covered by its type but no `inv` states its
// obligation, and the call stops.

#[thrust::trusted]
#[thrust::callable]
fn h<I: IteratorSpec<Item = i64>, J: Iterator<Item = i64>>(a: I, b: J)
where
    I::Item: thrust_models::Model,
{
    let _ = a.count();
    let _ = b.count();
}

fn main() {
    let f = |c: i64| move |x: i64| -> i64 { assert!(x < c); x };
    h((0..3).map(f(10)), (0..3).map(f(0))); //~ ERROR: a `pre!` stated of one value does not cover another
}
