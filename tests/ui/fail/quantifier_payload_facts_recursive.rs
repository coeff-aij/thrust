//@error-in-other-file: Unsat
//@ignore-on-host: not yet verifiable, the solver gives no answer within 280 s
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds ranges over the values of its type through a recursive enum's own
// payloads: the second element of a list is non-negative, as the enum's predicate applies itself
// to the tail. The twin of `pass/quantifier_payload_facts_recursive.rs`: no value has a negative
// one.
use thrust_models::exists;

enum L {
    Nil,
    Cons(u8, thrust_models::model::Box<L>),
}

#[thrust_macros::ensures(exists(|l: L| match l { L::Cons(_, b) => match *b { L::Cons(x, _) => x < 0, L::Nil => false }, L::Nil => false }))]
fn second_non_negative() {}

fn main() {}
