//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A recursive logic function with a parameter of an enum type with payload facts: its recursive
// call is assumed to have the result type's facts, as any call of a logic function is.
use thrust_models::model::UIntN;
use thrust_models::Model;

#[derive(PartialEq)]
pub enum E {
    A(UIntN<64>),
    B,
}

impl Model for E {
    type Ty = Self;
}

#[thrust_macros::logic]
#[thrust_macros::variant(n)]
fn cnt(e: E, n: usize) -> usize {
    if n <= 0 {
        0
    } else {
        cnt(e, n - 1)
    }
}

#[thrust_macros::ensures(result == cnt(e, n))]
fn f(e: E, n: usize) -> usize {
    if n == 0 { 0 } else { f(e, n - 1) }
}

fn main() {}
