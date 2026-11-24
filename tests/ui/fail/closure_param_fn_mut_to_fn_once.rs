//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::{exists, forall, model::{Closure, Mut}};

// A parameter bounded by `FnMut` where it is declared, handed to a function that calls it by
// value: that call is a call through `&mut` to the consumed state, so its postcondition is the one
// `post!` names at that state and some final state.
#[thrust_macros::requires(thrust_macros::pre!(g()))]
#[thrust_macros::ensures(thrust_macros::post!(g(), result))]
fn call_once<G: FnOnce() -> i64>(g: G) -> i64 {
    g()
}

#[thrust_macros::requires(forall(|c: Closure<F>| thrust_macros::pre!(c())))]
#[thrust_macros::ensures(exists(|h| thrust_macros::post!(Mut::new(f, h)(), result + 1)))]
fn consume<F: FnMut() -> i64>(f: F) -> i64 {
    call_once(f)
}

fn main() {}
