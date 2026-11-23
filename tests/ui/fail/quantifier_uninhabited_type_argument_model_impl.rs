//@compile-flags: -Adead_code -C debug-assertions=off

// A type without values below a type whose model a `Model` impl gives is found through its
// generic arguments: `Option<Infallible>` here, beside `Ghost<option::IntoIter<()>>`, whose model
// `Option<()>` has `Some(())`.
use std::convert::Infallible;
use thrust_models::{exists, Ghost};

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && exists(|p: (Ghost<std::option::IntoIter<()>>, Option<Infallible>)| p.0 == Some(()))); //~ ERROR: a quantified variable of type
    assert!(x == 1);
}
