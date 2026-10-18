//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The verified generic `g` calls the trusted `t` at no type parameter; `t` is a root in its own
// mode, trusted, and may run the ignored `bad`.

#[thrust::ignored]
fn bad() -> i32 {
    1
}

#[thrust::trusted]
#[thrust::callable]
fn t() -> i32 {
    bad()
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g<T>(x: T) -> i32 {
    t()
}

fn main() {
    g(1);
}
