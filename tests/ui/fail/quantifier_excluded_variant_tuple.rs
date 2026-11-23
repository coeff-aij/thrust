//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variant is excluded by position: `p.1`'s `Err` is, `p.0`'s is not, though both have the model
// sort `Result<Int, ()>`. The assumed statement is true of Rust values (`p.1` is always `Ok`).
use std::convert::Infallible;
use thrust_models::forall;

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|p: (Result<i64, ()>, Result<i64, Infallible>)| match p.1 { Ok(_) => true }));
    assert!(false);
}
