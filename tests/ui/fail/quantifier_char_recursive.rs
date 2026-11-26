//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds ranges over its type's values through a recursive enum's own
// payloads, also without `THRUST_INT_RANGE`: the second `char` of a list is a Unicode scalar
// value, as the enum's predicate applies itself to the tail. The twin of
// `pass/quantifier_char_recursive.rs`: no value has a larger one.
use thrust_models::exists;

enum L {
    Nil,
    Cons(char, thrust_models::model::Box<L>),
}

#[thrust_macros::ensures(exists(|l: L| match l { L::Cons(_, b) => match *b { L::Cons(c, _) => c > char::MAX, L::Nil => false }, L::Nil => false }))]
fn second_char_out_of_range() {}

fn main() {}
