//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The derived `PartialEq` compares the `PhantomData` field through the generic
// `PartialEq::eq` spec, whose parameter is instantiated at a singleton sort.

use std::marker::PhantomData;

#[derive(PartialEq)]
struct S {
    n: i64,
    m: PhantomData<i64>,
}

impl thrust_models::Model for S {
    type Ty = Self;
}

fn main() {
    let a = S {
        n: 1,
        m: PhantomData,
    };
    let b = S {
        n: 1,
        m: PhantomData,
    };
    assert!(a == b);
}
