//@error-in-other-file: verification error
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A variable a quantifier binds at a sequence ranges over sequences of values of the element type:
// no element is of a variant no value is of.
// The program must not verify. PCSat answers `unknown` here (about 40 s): the element guard is a
// `forall` in the premise of the assumed `forall`. Any verdict but `sat` is accepted until the
// solver answers `unsat`, which this expectation should then name.
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
    assert!(x == 1);
}
