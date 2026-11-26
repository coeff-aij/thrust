//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a quantifier binds at a type without values ranges over nothing, though the model of
// the type (`()` for `Infallible`) has a value: a `forall` over it holds and an `exists` does
// not.
#![feature(never_type)]
use std::convert::Infallible;
use thrust_models::{exists, forall};

#[thrust_macros::ensures(forall(|i: Infallible| false) && !exists(|i: Infallible| true))]
fn no_values() {}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|i: Infallible| false)
        && forall(|n: !| false));
    assert!(x == 1);
}
