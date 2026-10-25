//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the pass file: the body adds `usize::MAX`, so its value leaves the result type's
// range.
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
        cnt(e, n - 1) + 18446744073709551615usize
    }
}

#[thrust_macros::ensures(result == cnt(e, n))]
fn f(e: E, n: usize) -> usize {
    if n == 0 { 0 } else { f(e, n - 1) }
}

fn main() {}
