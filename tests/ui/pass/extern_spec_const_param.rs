//@check-pass
//@compile-flags: -C debug-assertions=off

// An extern spec of a local generic function over its const parameter is the contract of the
// function: its body, which reads `N`, is checked against it for every `N`.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 0)]
fn _extern_spec_f<const N: usize>() -> i64 {
    f::<N>()
}

fn f<const N: usize>() -> i64 {
    if N == 3 {
        0
    } else {
        0
    }
}

fn main() {
    assert!(f::<4>() == 0);
}
