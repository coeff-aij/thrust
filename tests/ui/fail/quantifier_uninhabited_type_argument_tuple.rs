//@compile-flags: -Adead_code -C debug-assertions=off

// Two instances of one enum in a tuple, one of them at a type without values, are rejected.
use std::convert::Infallible;
use thrust_models::forall;

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|p: (Result<i64, ()>, Result<i64, Infallible>)| match p.1 { Ok(_) => true })); //~ ERROR: a quantified variable of type
    assert!(x == 1);
}
