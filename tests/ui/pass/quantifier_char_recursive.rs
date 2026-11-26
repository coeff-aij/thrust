//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds ranges over its type's values through a recursive enum's own
// payloads, also without `THRUST_INT_RANGE`: the second `char` of a list is a Unicode scalar
// value, as the enum's predicate applies itself to the tail.
use thrust_models::forall;

enum L {
    Nil,
    Cons(char, thrust_models::model::Box<L>),
}

#[thrust_macros::ensures(forall(|l: L| match l { L::Cons(_, b) => match *b { L::Cons(c, _) => c <= char::MAX, L::Nil => true }, L::Nil => true }))]
fn second_char_in_range() {}

fn main() {}
