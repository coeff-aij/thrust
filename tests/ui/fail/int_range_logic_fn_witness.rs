//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Logic functions whose results have facts in a tuple, a generic enum at an instance and a `&mut`:
// outside their parameters' range their value is a fixed one with the facts, not the body's.
use thrust_models::model::{Mut, UIntN};
use thrust_models::Model;

#[derive(PartialEq)]
pub enum R<A> {
    Ok(A),
    Err(A),
}

impl<A> Model for R<A> {
    type Ty = Self;
}

#[thrust_macros::logic]
fn r(n: usize) -> R<UIntN<64>> {
    R::Ok(n)
}

#[thrust_macros::logic]
fn t(n: usize) -> (UIntN<64>, bool) {
    (n, true)
}

#[thrust_macros::logic]
fn m(n: usize) -> Mut<UIntN<64>> {
    Mut::new(n, n)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(r(n + 18446744073709551616u128) == R::Ok(n + 18446744073709551616u128))]
fn f(n: usize) {}

fn main() {}
