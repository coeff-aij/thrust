//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::Int;
use thrust_models::Model;

// `B::ix` is not injective, so `B` cannot prove the law.

// A law over a trait's logic function: each implementation proves it, and a generic function
// (`equal_by_ix`) gets it as a premise of the function standing for `ix` at its parameter.
#[thrust_macros::context]
trait Ix: Copy + Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty> + PartialEq,
{
    #[thrust_macros::logic]
    fn ix(self) -> Int;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::ix(*x) == Self::ix(*y))]
    #[thrust_macros::ensures(*x == *y)]
    fn ix_injective(x: &Self, y: &Self);
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

    fn ix_injective(x: &A, y: &A) {}
}

#[derive(Clone, Copy)]
struct B(i64);

impl Model for B {
    type Ty = (Int,);
}

#[thrust_macros::context]
impl Ix for B {
    #[thrust_macros::logic]
    fn ix(self) -> Int {
        self.0 * self.0
    }

    fn ix_injective(x: &B, y: &B) {}
}

#[thrust_macros::context]
#[thrust_macros::requires(T::ix(*x) == T::ix(*y))]
#[thrust_macros::ensures(*x == *y)]
fn equal_by_ix<T: Ix>(x: &T, y: &T)
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty> + PartialEq,
{
}

fn main() {}
