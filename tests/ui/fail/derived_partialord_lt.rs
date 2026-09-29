//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The struct's model has no order of its own, so `<` compares through the derived
// `partial_cmp`, which compares the fields in order.
#[derive(PartialEq, PartialOrd)]
struct P {
    a: i64,
    b: i64,
}

impl thrust_models::Model for P {
    type Ty = P;
}

#[thrust_macros::requires(x == P { a: 1, b: 5 } && y == P { a: 1, b: 5 })]
#[thrust_macros::ensures(true)]
fn check(x: P, y: P) {
    assert!(x < y);
}

fn main() {
    check(P { a: 1, b: 5 }, P { a: 1, b: 5 });
}
