//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/partial_move_mut_ref_assoc.rs`: the write through the `&mut` moved out of
// `t` reaches `a`.

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
    assert!(a == 5);
}
