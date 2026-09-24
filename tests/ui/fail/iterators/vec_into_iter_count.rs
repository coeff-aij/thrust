//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// The loop steps the count by two per element, so it no longer counts the elements of the
// vector it consumed.

#[thrust_macros::context]
#[thrust_macros::requires(v.len() >= 0)]
#[thrust_macros::ensures(result == v.len())]
fn count<T>(v: Vec<T>) -> usize
    where T: thrust_models::Model, T::Ty: PartialEq
{
    let mut it = v.into_iter();
    let mut n = 0;
    while let Some(_x) = it.next() {
        thrust_macros::invariant!(
            |it: std::vec::IntoIter<T>, n: usize, v: thrust_models::FnParam<Vec<T>>|
                it.0 == v.at_entry() && n == it.1 && it.1 <= it.0.len());
        n = n + 2;
    }
    n
}

fn main() {}
