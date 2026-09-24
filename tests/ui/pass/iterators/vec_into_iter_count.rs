//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// `vec::IntoIter` at a type parameter element type: the consuming `into_iter`, which starts at
// position 0 over the sequence the vector held. The vector is gone by the loop header, so the
// invariant names its entry value through `FnParam` rather than the parameter itself.

#[thrust_macros::context]
#[thrust_macros::requires(v.length >= 0)]
#[thrust_macros::ensures(result == v.length)]
fn count<T>(v: Vec<T>) -> usize
    where T: thrust_models::Model, T::Ty: PartialEq
{
    let mut it = v.into_iter();
    let mut n = 0;
    while let Some(_x) = it.next() {
        thrust_macros::invariant!(
            |it: std::vec::IntoIter<T>, n: usize, v: thrust_models::FnParam<Vec<T>>|
                it.0 == v.at_entry() && n == it.1 && it.1 <= it.0.length);
        n = n + 1;
    }
    n
}

fn main() {}
