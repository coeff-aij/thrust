//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `t.0` holds a `&mut` through a field of an associated type, so dropping `t` after the move
// must not resolve it: `a` is 5 at the assertion.

use std::marker::PhantomData;

trait Tr {
    type Out;
}

struct X<'a>(PhantomData<&'a ()>);

impl<'a> Tr for X<'a> {
    type Out = Option<&'a mut i32>;
}

struct In<T: Tr> {
    r: T::Out,
}

fn main() {
    let mut a = 0;
    let t = (In::<X> { r: Some(&mut a) }, 1);
    let y = t.0;
    if let Some(r) = y.r {
        *r = 5;
    }
    assert!(a == 0);
}
