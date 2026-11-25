//@check-pass
//@compile-flags: -C debug-assertions=off
use thrust_models::Model;
#[derive(PartialEq)]
enum E {
    A(i64),
    B,
}

impl Model for E {
    type Ty = E;
}

#[thrust_macros::requires(x == E::A(1) && y == E::B)]
#[thrust_macros::ensures(true)]
fn check(x: E, y: E) {
    assert!(x != y);
}

fn main() {
    check(E::A(1), E::B);
}
