//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_under_trusted_main.rs`: `S`'s `m` is analyzed.

struct S(i32);

impl thrust_models::Model for S {
    type Ty = Self;
}

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == true)]
    fn m(&self) -> bool;
}

impl Tr for S {
    fn m(&self) -> bool {
        true
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g<T: Tr>(x: &T) {
    assert!(x.m());
}

#[thrust::trusted]
#[thrust::callable]
fn main() {
    g(&S(1));
}
