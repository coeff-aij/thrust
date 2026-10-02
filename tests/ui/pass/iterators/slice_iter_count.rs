//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `while let Some(_) = it.next()` over `<[T]>::iter` at a type parameter element type. The
// loop leaves through the second disjunct of `next`'s postcondition, which puts the cursor at
// or past the end; the invariant's upper bound turns that into equality with the length.
//
// The length of a slice is not known to be non-negative -- nothing in the model says so -- so
// the bound has to be assumed on entry.

#[thrust_macros::context]
#[thrust_macros::requires((*s).len() >= 0)]
#[thrust_macros::ensures(result == (*s).len())]
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
    assert!(n == s.len());
    n
}

fn main() {}
