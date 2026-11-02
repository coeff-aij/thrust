//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/dyn_trait_to_trusted.rs`: the method accepts every argument.

trait Call {
    fn call(&self, x: &i64) -> bool;
}

struct S;

impl Call for S {
    fn call(&self, x: &i64) -> bool {
        *x > 0
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn run(c: &dyn Call) -> bool {
    c.call(&100)
}

fn main() {
    run(&S);
}
