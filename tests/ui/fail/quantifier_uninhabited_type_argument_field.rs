//@compile-flags: -Adead_code -C debug-assertions=off

// A type without values in a field type's generic argument is found through the fields:
// `E::A`'s `Option<Infallible>` has values, so `A` is not excluded, yet its model has
// `A(Some(()))`.
use std::convert::Infallible;
use thrust_models::forall;

enum E {
    A(Option<Infallible>),
    B,
}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|e: E| match e { E::A(o) => match o { None => true }, E::B => true })); //~ ERROR: a quantified variable of type `E` is not supported: it holds `std::convert::Infallible`
    assert!(x == 1);
}
