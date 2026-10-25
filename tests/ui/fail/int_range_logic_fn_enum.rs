//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait's logic function at an enum whose payload is a `UIntN<64>`: a generic function verified
// once makes a ghost value from it, and a caller assumes the facts of the result's type. The
// definition is checked against them: here its value is at least `2^64` (model arithmetic is
// unbounded), and the expected error is that check.
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
        E::A(n + 18446744073709551616u128)
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == T::big(t, n))]
fn mk<T: Mk>(t: T, n: usize) -> Ghost<T>
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    thrust_macros::ghost!(|t: T, n: usize| -> T { T::big(t, n) })
}

#[thrust::callable]
fn f(e: E, x: usize) {
    if x == 0 {
        let g = mk(e, x);
        assert!(x == 0);
    }
}

fn main() {}
