//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/dyn_trait_coerce_unsized.rs`: the field is coerced to `&dyn Shape` before
// `W` is built, which is a packing of its own.

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
    let w: W<dyn Shape> = W(&t);
    assert!(w.0.sides() >= 3);
}
