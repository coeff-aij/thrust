//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/dyn_trait_closure_to_trusted.rs`: the closure accepts every argument.

trait Call {
    fn call(&self, x: &i64) -> bool;
}

impl<F: Fn(&i64) -> bool> Call for F {
    fn call(&self, x: &i64) -> bool {
        self(x)
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn run(c: &dyn Call) -> bool {
    c.call(&100)
}

fn main() {
    let f = |x: &i64| *x > 0;
    run(&f);
}
