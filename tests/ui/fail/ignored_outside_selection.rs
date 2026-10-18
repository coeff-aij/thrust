//@error-in-other-file: is `#[thrust::ignored]`
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=f,h

// With `h` selected, its call of the ignored `helper` is verified code.

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
