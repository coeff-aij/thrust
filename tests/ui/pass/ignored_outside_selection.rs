//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=f

// The twin of `fail/ignored_outside_selection.rs`: `h` is outside `THRUST_VERIFY_ONLY` and trusted
// for its contract, so it may run the ignored `helper`.

#[thrust::ignored]
fn helper(x: i32) -> i32 {
    x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h(x: i32) -> i32 {
    helper(x)
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f(x: i32) -> i32 {
    h(x)
}

fn main() {}
