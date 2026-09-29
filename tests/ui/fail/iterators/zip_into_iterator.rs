//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// The invariant is off by one, so it already fails to hold at the first iteration.

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
                it.0.1 == it.1.1 + 1 && it.0.0.len() == it.1.0.len());
    }
}

fn main() {}
