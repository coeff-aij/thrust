//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A logic function whose result is a recursive enum holding a `UIntN<64>`: no finite formula
// checks its value's facts, so the definition is an error naming the type.
use thrust_models::model::UIntN;
use thrust_models::Model;

#[derive(PartialEq)]
pub enum L {
    Nil,
    Cons(UIntN<64>, Box<L>),
}

impl Model for L {
    type Ty = Self;
}

#[thrust_macros::logic] //~ ERROR: cannot be checked
fn nil(n: usize) -> L {
    L::Nil
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == nil(n))]
fn g(n: usize) -> L {
    unimplemented!()
}

#[thrust::callable]
fn f(x: usize) {
    let r = g(x);
}

fn main() {}
