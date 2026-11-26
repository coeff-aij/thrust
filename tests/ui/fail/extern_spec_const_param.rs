//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// An extern spec of a local generic function over its const parameter is the contract of the
// function: its body is checked against it for every `N`, and breaks it at `N = 3`.

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 0)]
fn _extern_spec_f<const N: usize>() -> i64 {
    f::<N>()
}

fn f<const N: usize>() -> i64 {
    if N == 3 {
        1
    } else {
        0
    }
}

fn main() {
    assert!(f::<4>() == 0);
}
