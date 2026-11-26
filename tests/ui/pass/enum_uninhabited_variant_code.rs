//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// Code that reaches a variant no value is of, which its datatype has no constructor for, is never
// run: a `match` arm on it, a value built of it from a parameter without values. An enum none of
// whose variants has values (`A`), and one without variants (`Void`), have a datatype whose one
// constructor stands for no Rust value.
use std::convert::Infallible;

enum Void {}

enum A {
    X(Void),
}

enum E {
    Bad(Infallible),
    Ok(i64),
    Empty(A),
}

impl thrust_models::Model for E {
    type Ty = E;
}

#[thrust_macros::ensures(result == 1)]
fn read(e: E) -> i64 {
    match e {
        E::Bad(v) => match v {},
        E::Ok(_) => 1,
        E::Empty(a) => match a {
            A::X(v) => match v {},
        },
    }
}

#[thrust_macros::ensures(false)]
fn build(x: Infallible) -> E {
    E::Bad(x)
}

fn main() {
    let e = E::Ok(3);
    assert!(read(e) == 1);
}
