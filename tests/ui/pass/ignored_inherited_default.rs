//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_inherited_default.rs`: the default `d` that `S` inherits is analyzed.

trait Tr {
    fn d(&self) -> i32 {
        0
    }
}

struct S;

impl Tr for S {}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h<T: Tr>(x: &T) -> i32 {
    x.d()
}

fn main() {
    h(&S);
}
