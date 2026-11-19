//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=main
// A closure `d` captured by the closure `c` that a generic `own` hands to the trusted `t` at its
// `Fn`-bounded parameter `F`; `t` also receives `d` at `Y`, whose call bound is
// `for<'a> &'a Y: Fn(i32)`, and calls it at 0, where it panics.
// The hand-over at `X` covers the closure `c` only, not `d` found in its capture; `d` reaches
// the trusted `t` uncounted, so the call stops.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t<F: Fn(i32), Y>(f: F, y: Y)
where
    for<'a> &'a Y: Fn(i32),
{
    f(1);
    call_at_zero(&y);
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn call_at_zero<G: Fn(i32)>(g: G) {
    g(0);
}

#[thrust_macros::requires(thrust_models::forall(|a: i32| thrust_macros::pre!(x(a))))]
#[thrust_macros::ensures(true)]
fn own<X: Fn(i32), Y>(x: X, y: Y)
where
    for<'a> &'a Y: Fn(i32),
{
    t(x, y);
}

fn main() {
    let d = |v: i32| assert!(v > 0); //~ ERROR: without an analyzed call handing it over
    let c = move |_: i32| d(1);
    own(c, d);
}
