//@compile-flags: -Adead_code -C debug-assertions=off

// A field type is read at the ADT's arguments: `Outer<X>`'s field `Option<I::A>` is
// `Option<Infallible>`, whose model has `Some(())`.
use std::convert::Infallible;
use thrust_models::forall;

trait Tr {
    type A;
}

struct X;

impl Tr for X {
    type A = Infallible;
}

struct Outer<I: Tr> {
    h: Option<I::A>,
}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|o: Outer<X>| match o { Outer { h: Some(_) } => false, Outer { h: None } => true })); //~ ERROR: a quantified variable of type `Outer<X>` is not supported: it holds `std::convert::Infallible`
    assert!(x == 1);
}
