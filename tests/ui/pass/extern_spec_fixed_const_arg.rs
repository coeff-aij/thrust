//@check-pass
//@compile-flags: -C debug-assertions=off

// An extern spec of a local generic function at a fixed const argument covers only that
// instance: the body of `f` meets the spec at `N = 3`, and not at the other instances.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 0)]
fn _extern_spec_f() -> i64 {
    f::<3>()
}

fn f<const N: usize>() -> i64 {
    if N == 3 {
        0
    } else {
        1
    }
}

fn main() {
    assert!(f::<3>() == 0);
}
