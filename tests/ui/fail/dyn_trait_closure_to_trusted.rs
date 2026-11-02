//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A closure behind a trait object handed to code Thrust does not analyze, through a blanket impl
// whose method the trait gives no contract: the closure must accept every argument.

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
    let f = |x: &i64| {
        assert!(*x < 10);
        *x > 0
    };
    run(&f);
}
