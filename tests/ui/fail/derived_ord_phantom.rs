//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The order generated from a derived `PartialOrd` reads each field at its declaration index, past
// a `PhantomData` field that compares equal.

use std::marker::PhantomData;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct P {
    a: u8,
    m: PhantomData<u8>,
    b: i64,
}

fn main() {
    let x = P { a: 1, m: PhantomData, b: 5 };
    let y = P { a: 1, m: PhantomData, b: 7 };
    assert!(y < x);
}
