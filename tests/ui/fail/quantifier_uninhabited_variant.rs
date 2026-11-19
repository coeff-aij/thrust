//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a quantifier binds at an enum type does not range over a variant whose payload no
// value has, which a `match` may leave out.
use std::convert::Infallible;
use thrust_models::forall;

enum E {
    A(Infallible),
    B(i64),
}

#[thrust_macros::ensures(forall(|e: E| match e { E::B(_) => true }))]
fn uninhabited_variants_left_out() {}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|e: E| match e { E::B(_) => true }));
    assert!(x == 1);
}
