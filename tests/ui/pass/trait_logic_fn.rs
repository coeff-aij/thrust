//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::model::Int;
use thrust_models::Model;

// A trait's logic function without a body is, at a type parameter, one function for every
// implementation (`same`), and at an implementing type that implementation's definition
// (`both`, which uses `same` at two of them).
#[thrust_macros::context]
trait Ix: Copy + Model
where
    <Self as Model>::Ty: Model<Ty = <Self as Model>::Ty>,
{
    #[thrust_macros::logic]
    fn ix(self) -> Int;

    #[thrust_macros::ensures(result == Self::ix(self))]
    fn index(self) -> i64;
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

    fn index(self) -> i64 {
        self.0
    }
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
        self.0 + 1
    }

    fn index(self) -> i64 {
        self.0 + 1
    }
}

#[thrust_macros::context]
#[thrust_macros::requires(T::ix(x) == T::ix(y))]
#[thrust_macros::ensures(result)]
fn same<T: Ix>(x: T, y: T) -> bool
where
    <T as Model>::Ty: Model<Ty = <T as Model>::Ty>,
{
    x.index() == y.index()
}

#[thrust_macros::requires(a.0 == a2.0 && b.0 == b2.0)]
#[thrust_macros::ensures(result)]
fn both(a: A, a2: A, b: B, b2: B) -> bool {
    same(a, a2) && same(b, b2)
}

fn main() {}
