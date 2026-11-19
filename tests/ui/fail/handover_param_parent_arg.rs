//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=main
// The program of r1_param_capture with `c` written in a generic `mk` whose type parameter is the
// type of `d`: `c` neither captures nor calls `d`.
// The hand-over at `X` covers the closure `c` only, not `d` found in its parent type argument; `d` reaches
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

fn mk<T>(_: &T) -> impl Fn(i32) {
    |_: i32| ()
}

fn main() {
    let d = |v: i32| assert!(v > 0); //~ ERROR: without an analyzed call handing it over
    let c = mk(&d);
    own(c, d);
}
