//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trusted `main` is a root of the ignored check: it runs the verified `g` at `S`, which runs
// `S`'s ignored `m`.

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
fn g<T: Tr>(x: &T) {
    assert!(x.m());
}

#[thrust::trusted]
#[thrust::callable]
fn main() {
    g(&S(1));
}
