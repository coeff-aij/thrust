//@compile-flags: -Adead_code -C debug-assertions=off

// A variable at a type that holds a type without values as a generic argument is rejected: the
// model of `Result<i64, Infallible>` has `Err(())`, which no Rust value is, and no exclusion of
// the definition covers it (`Result<T, E>`'s `Err` has values in general).
use std::convert::Infallible;
use thrust_models::forall;

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|r: Result<i64, Infallible>| match r { Ok(_) => true })); //~ ERROR: a quantified variable of type `std::result::Result<i64, std::convert::Infallible>` is not supported
    assert!(x == 1);
}
