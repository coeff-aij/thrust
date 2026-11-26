//@compile-flags: -C debug-assertions=off
// An extern spec of a trusted function states the contract callers use, so it has the same
// requirement as the trusted function's own contract.

#[thrust::trusted]
fn run<Y: thrust_models::Model>(y: Y) where for<'a> &'a Y: Fn(i32) { call_at_zero(&y) }

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn call_at_zero<G: Fn(i32)>(g: G) { g(0); }

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn _extern_spec_run<Y: thrust_models::Model>(y: Y) where for<'a> &'a Y: Fn(i32) { //~ ERROR: a closure run through a bound on `&'a Y` cannot have its `pre!` stated
    run(y)
}

fn main() {}
