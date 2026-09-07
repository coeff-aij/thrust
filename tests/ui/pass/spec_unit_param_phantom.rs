//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The derived `PartialEq` compares the `PhantomData` field through the generic
// `PartialEq::eq` spec, instantiating its parameter at a singleton sort.

use std::marker::PhantomData;

#[derive(PartialEq)]
struct S<T> {
    n: i64,
    m: PhantomData<T>,
}

impl<T> thrust_models::Model for S<T> {
    type Ty = Self;
}

fn main() {
    let a: S<i64> = S {
        n: 1,
        m: PhantomData,
    };
    let b: S<i64> = S {
        n: 1,
        m: PhantomData,
    };
    assert!(a == b);
}
