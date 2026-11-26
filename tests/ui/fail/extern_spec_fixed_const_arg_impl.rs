//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// An extern spec of a method of a local impl at a fixed const argument of the impl covers only
// that instance: the body of `get` is checked against the spec at `N = 3`, where it breaks it.

struct A<const N: usize>;

impl<const N: usize> A<N> {
    fn get() -> i64 {
        1
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 0)]
fn _extern_spec_get() -> i64 {
    A::<3>::get()
}

fn main() {
    assert!(A::<3>::get() == 0);
}
