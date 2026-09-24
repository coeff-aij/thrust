//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// A slice whose element type is a type parameter. `<[T] as Model>::Ty` is of no use here: with
// a `Model` bound it normalizes to a `Seq` that still carries `<T as Model>::Ty`, and without
// one it does not normalize at all. The model is built from the shape of the type instead, the
// same `(elements, length)` pair a `Vec` gets.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*s).len())]
fn size<T>(s: &[T]) -> usize
    where T: thrust_models::Model, T::Ty: PartialEq
{
    s.len()
}

#[thrust_macros::requires((*s).len() > 0)]
#[thrust_macros::ensures(*result == (*s)[0])]
fn head<T>(s: &[T]) -> &T
    where T: thrust_models::Model, T::Ty: PartialEq
{
    &s[s.len() - 1]
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*a).len())]
fn size_fixed<T>(a: &[T; 3]) -> usize
    where T: thrust_models::Model, T::Ty: PartialEq
{
    a.len()
}

fn ignore_unbounded<T>(s: &[T]) -> usize {
    let _ = s;
    0
}

fn main() {
    let a: [i64; 3] = [7, 8, 9];
    assert!(size(&a) == 3);
    assert!(*head(&a) == 7);
    assert!(size_fixed(&a) == 3);
    assert!(ignore_unbounded(&a) == 0);
}
