//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The prophecy pair of a `&mut [T]` at a type parameter element type, and the call site that
// instantiates it.

#[thrust_macros::requires((*s).length > 0)]
#[thrust_macros::ensures((!s).array[0] == v && (!s).length == (*s).length)]
fn set_head<T>(s: &mut [T], v: T)
    where T: thrust_models::Model, T::Ty: PartialEq
{
    *s.last_mut().unwrap() = v;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures((*result).length == 2)]
fn slice() -> &'static mut [i64] {
    unimplemented!()
}

fn main() {
    let s = slice();
    set_head(s, 5);
    assert!(s[0] == 5);
}
