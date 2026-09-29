//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// `std::iter::zip` takes `IntoIterator` arguments, not iterators already: passing two owned
// `Vec`s, rather than calling `.iter()` on each first, exercises the `IntoIteratorSpec` side of
// the vocabulary (`Vec<T>::into_iter` starting each half at position 0 over the vector it
// consumed). Equal-length vectors keep the two halves at the same position throughout.

#[thrust_macros::context]
#[thrust_macros::requires(a.len() == b.len())]
fn in_lockstep<T, U>(a: Vec<T>, b: Vec<U>)
    where T: thrust_models::Model, T::Ty: PartialEq,
          U: thrust_models::Model, U::Ty: PartialEq
{
    let mut it = std::iter::zip(a, b);
    while let Some(_pair) = it.next() {
        thrust_macros::invariant!(
            |it: core::iter::Zip<std::vec::IntoIter<T>, std::vec::IntoIter<U>>|
                it.0.1 == it.1.1 && it.0.0.len() == it.1.0.len());
    }
}

fn main() {}
