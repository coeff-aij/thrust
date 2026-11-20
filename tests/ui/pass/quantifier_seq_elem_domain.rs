//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable a quantifier binds at a sequence ranges over sequences of values of the element type:
// no element is of a variant no value is of.
use std::convert::Infallible;
use thrust_models::forall;
use thrust_models::model::Seq;

enum E {
    A(Infallible),
    B(i64),
}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|s: Seq<E>| s.len() == 0 || match s[0] { E::B(_) => true, E::A(_) => false }));
    assert!(x == 0);
}
