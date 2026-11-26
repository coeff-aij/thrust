//@error-in-other-file: Unsat
use thrust_models::Model;
#[derive(PartialEq)]
pub enum X {
    A(i64),
    B(bool),
}

impl Model for X {
    type Ty = X;
}

#[thrust_macros::requires(x == X::A(1))]
#[thrust_macros::ensures(true)]
fn test(x: X) {
    if let X::A(i) = x {
        assert!(i == 2);
    } else {
        loop {}
    }
}

fn main() {
    test(X::A(1));
}
