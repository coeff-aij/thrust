//@check-pass
//@compile-flags: -Adead_code -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable `forall` or `exists` binds at an unsigned type ranges over the values `>= 0`, and a
// sequence's unsigned elements, and the unsigned fields of its elements, are `>= 0`, in every mode.

use thrust_models::forall;

#[thrust_macros::ensures(forall(|i: usize| i >= 0))]
fn binder() {}

#[thrust_macros::requires(s.len() > 0)]
#[thrust_macros::ensures(s[0] >= 0)]
fn elem(s: &[u32]) {}

struct P {
    x: u32,
}

impl thrust_models::Model for P {
    type Ty = Self;
}

#[thrust_macros::requires(s.len() > 0)]
#[thrust_macros::ensures(s[0].x >= 0)]
fn field(s: &[P]) {}

fn main() {}
