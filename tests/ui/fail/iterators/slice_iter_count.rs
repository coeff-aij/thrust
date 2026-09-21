//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The loop visits each element of the slice exactly once, so it counts the length and not one
// more than the length. A slice of length 0 already refutes the claim.

#[thrust_macros::context]
#[thrust_macros::requires((*s).len() >= 0)]
#[thrust_macros::ensures(result == (*s).len() + 1)]
fn count<T>(s: &[T]) -> usize
    where T: thrust_models::Model, T::Ty: PartialEq
{
    let mut it = s.iter();
    let mut n = 0;
    while let Some(_x) = it.next() {
        thrust_macros::invariant!(|it: core::slice::Iter<'_, T>, n: usize, s: &[T]|
            it.0 == *s && n == it.1 && it.1 <= it.0.len());
        n = n + 1;
    }
    assert!(n == s.len() + 1);
    n
}

fn main() {}
