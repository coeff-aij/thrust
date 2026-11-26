//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A `match` whose arms all name variants without values (`NeverP::X`) is reached by no Rust value.
// In a logic function, which is defined at every value of its parameters' sorts, it is a fixed value
// of its type, and the function's other arms keep their values.
use std::convert::Infallible;
use thrust_models::model::Int;
use thrust_models::Model;

struct Pair(Infallible, i64);

enum NeverP {
    X(Pair),
}

impl Model for NeverP {
    type Ty = NeverP;
}

#[thrust_macros::logic]
fn lf(o: Option<NeverP>) -> Int {
    match o {
        Some(n) => match n {
            NeverP::X(_) => 1,
        },
        None => 0,
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(lf(None) == 0)]
fn f() {}

fn main() {
    f();
}
