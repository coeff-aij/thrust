//@error-in-other-file: trait objects are made only as
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Coercing a `CoerceUnsized` struct to one holding a trait object is not supported: it would skip
// the checks of packing.

#![feature(coerce_unsized, unsize)]
use std::marker::Unsize;
use std::ops::CoerceUnsized;

#[thrust_macros::context]
trait Shape {
    #[thrust_macros::ensures(result >= 3)]
    fn sides(&self) -> u32;
}

struct Tri;

impl thrust_models::Model for Tri {
    type Ty = ();
}

impl Shape for Tri {
    fn sides(&self) -> u32 {
        3
    }
}

struct W<'a, T: ?Sized>(&'a T);

impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<W<'a, U>> for W<'a, T> {}

fn main() {
    let t = Tri;
    let w0: W<Tri> = W(&t);
    let w: W<dyn Shape> = w0;
    assert!(w.0.sides() >= 3);
}
