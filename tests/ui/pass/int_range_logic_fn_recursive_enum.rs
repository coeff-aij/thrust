//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_INT_RANGE=conversions THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of the fail file: the enum is not recursive, so the definition's value is checked.
use thrust_models::model::UIntN;
use thrust_models::Model;

#[derive(PartialEq)]
pub enum L {
    Nil,
    Cons(UIntN<64>, Box<UIntN<64>>),
}

impl Model for L {
    type Ty = Self;
}

#[thrust_macros::logic]
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
