//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the fail file: the logic function's value at an enum whose payload is a
// `UIntN<64>` is in range, so its definition meets the facts of its result type.
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
