//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Without `THRUST_INT_RANGE`, a law variable of an unsigned type is non-negative, as its proof
// assumes. The twin of `pass/uint_law.rs`: only a law over negative values would give the result.
use thrust_models::model::Int;
use thrust_models::Model;

#[thrust_macros::context]
trait Ix: Copy + Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::logic]
    fn ix(self) -> Int;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::ix(*x) == Self::ix(*x) && *n >= 0)]
    fn nonneg(x: &Self, n: &usize);
}

#[derive(Clone, Copy)]
struct A(i64);

impl Model for A {
    type Ty = (Int,);
}

#[thrust_macros::context]
impl Ix for A {
    #[thrust_macros::logic]
    fn ix(self) -> Int {
        self.0
    }

    fn nonneg(x: &A, n: &usize) {}
}

#[thrust_macros::context]
#[thrust_macros::requires(T::ix(*x) == 0)]
#[thrust_macros::ensures(T::ix(*x) == 1)]
fn at_zero<T: Ix>(x: &T)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
}

fn main() {}
