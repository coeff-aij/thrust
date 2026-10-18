//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A field whose type is an associated type is dropped as the type it stands for: dropping `_h`
// runs `W`'s destructor, which sets `a` to 1.

use std::marker::PhantomData;

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 1;
    }
}

trait Tr {
    type Out;
}

struct X<'a>(PhantomData<&'a ()>);

impl<'a> Tr for X<'a> {
    type Out = W<'a>;
}

struct H<T: Tr> {
    x: T::Out,
}

fn main() {
    let mut a = 0;
    {
        let _h = H::<X> { x: W(&mut a) };
    }
    assert!(a == 0);
}
