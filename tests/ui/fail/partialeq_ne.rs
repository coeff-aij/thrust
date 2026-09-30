//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[derive(PartialEq)]
enum E {
    A(i64),
    B,
}

impl thrust_models::Model for E {
    type Ty = E;
}

#[thrust_macros::requires(x == E::A(1i64) && y == E::A(1i64))]
#[thrust_macros::ensures(true)]
fn check(x: E, y: E) {
    assert!(x != y);
}

fn main() {
    check(E::A(1), E::A(1));
}
