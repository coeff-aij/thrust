//@compile-flags: -C debug-assertions=off -C opt-level=3
//@rustc-env: THRUST_OPTIMIZED_MIR=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// At `-C opt-level=3` rustc would inline the verified `g` into the trusted `t`; Thrust reads MIR
// without inlining, so `g::<S>` stays verified code and its call of `S`'s ignored `m` stops.

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
    #[thrust::ignored]
    fn m(&self) -> bool { //~ ERROR: a verified function can run it
        false
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
