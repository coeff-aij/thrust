//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A checked `exists` whose variable the formula reads only through one payload field needs a
// witness with the facts of that field only.
use thrust_models::exists;

enum E {
    A(u64, u64),
    B(u64),
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(exists(|e: E| match e { E::A(a, _) => a < 0, E::B(_) => false }))]
fn some_a_zero() {}

fn main() {}
