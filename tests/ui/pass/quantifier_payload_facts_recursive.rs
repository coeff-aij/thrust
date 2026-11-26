//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds ranges over the values of its type through a recursive enum's own
// payloads: the second element of a list is non-negative, as the enum's predicate applies itself
// to the tail.
use thrust_models::forall;

enum L {
    Nil,
    Cons(u8, thrust_models::model::Box<L>),
}

#[thrust_macros::ensures(forall(|l: L| match l { L::Cons(_, b) => match *b { L::Cons(x, _) => x >= 0, L::Nil => true }, L::Nil => true }))]
fn second_non_negative() {}

fn main() {}
