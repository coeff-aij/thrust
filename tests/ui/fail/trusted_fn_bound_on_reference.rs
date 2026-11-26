//@compile-flags: -C debug-assertions=off
// A trusted contract must state the `pre!` of every closure its body runs, and a `pre!` names a
// closure type parameter, so a closure run through `for<'a> &'a Y: Fn(..)` cannot be covered.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn t<Y>(y: Y) where for<'a> &'a Y: Fn(i32) { //~ ERROR: a closure run through a bound on `&'a Y` cannot have its `pre!` stated
    call_at_zero(&y)
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn call_at_zero<G: Fn(i32)>(g: G) { g(0); }

fn main() {
    let d = |a: i32| assert!(a > 0);
    t(d);
}
