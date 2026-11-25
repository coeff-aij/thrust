//@check-pass
//@compile-flags: -C debug-assertions=off

// An extern spec of a method of a local impl at a fixed const argument of the impl covers only
// that instance: the body of `get` meets the spec at `N = 3`, and not at the other instances.

struct A<const N: usize>;

impl<const N: usize> A<N> {
    fn get() -> i64 {
        if N == 3 {
            0
        } else {
            1
        }
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
