//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables

// A `match` whose arms all name variants without values is a fixed value of its type; at a type
// Thrust builds no value of (a function pointer, `pick` at `T = fn(i64) -> i64`) it is an error.
use std::convert::Infallible;
use thrust_models::{forall, Model};

struct Pair(Infallible, i64);

enum NeverP {
    X(Pair),
}

impl Model for NeverP {
    type Ty = NeverP;
}

#[thrust_macros::logic]
fn pick<T>(n: NeverP, t: T) -> T {
    match n { //~ ERROR: a `match` that no Rust value reaches is not supported at the type
        NeverP::X(_) => t,
    }
}

#[thrust_macros::ensures(forall(|n: NeverP| pick::<T>(n, t) == t))]
fn f<T>(t: T) {}

fn g(x: i64) -> i64 {
    x
}

fn main() {
    f(g as fn(i64) -> i64);
}
