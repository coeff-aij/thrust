//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_assoc.rs`: dropping `_h` runs `W`'s destructor, which sets `a`.

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
    assert!(a == 1);
}
