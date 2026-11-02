//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A method the trait gives no contract is called through the trait object only by code Thrust
// does not analyze, so it must accept every argument.

trait Call {
    fn call(&self, x: &i64) -> bool;
}

struct S;

impl Call for S {
    fn call(&self, x: &i64) -> bool {
        assert!(*x < 10);
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
