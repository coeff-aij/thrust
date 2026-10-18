//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=3
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_inlined_into_trusted.rs`: `S`'s `m` is analyzed.

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
#[inline(always)]
fn g<T: Tr>(x: &T) -> i32 {
    assert!(x.m());
    1
}

#[thrust::trusted]
#[thrust::callable]
fn t() -> i32 {
    g(&S(1))
}

fn main() {
    t();
}
