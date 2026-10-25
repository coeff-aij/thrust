//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `big` at an enum with a `UIntN<64>` payload is `E::A(n)`, which has the result's facts wherever
// `n` has those of `usize`, and the generic `mk` applies it at `n + 2^64`, outside them. A logic
// function's value there is a fixed value of its result type, so the caller's facts of the result
// hold and do not make `assert!(x == 1)` vacuous.
use thrust_models::model::UIntN;
use thrust_models::{Ghost, Model};

#[derive(PartialEq)]
pub enum E {
    A(UIntN<64>),
    B,
}

impl Model for E {
    type Ty = Self;
}

#[thrust_macros::context]
trait Mk: Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::logic]
    fn big(self, n: usize) -> Self;
}

#[thrust_macros::context]
impl Mk for E {
    #[thrust_macros::logic]
    fn big(self, n: usize) -> E {
        E::A(n)
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == T::big(t, n + 18446744073709551616u128))]
fn mk<T: Mk>(t: T, n: usize) -> Ghost<T>
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    thrust_macros::ghost!(|t: T, n: usize| -> T { T::big(t, n + 18446744073709551616u128) })
}

#[thrust::callable]
fn f(e: E, x: usize) {
    if x == 0 {
        let g = mk(e, x);
        assert!(x == 1);
    }
}

fn main() {}
