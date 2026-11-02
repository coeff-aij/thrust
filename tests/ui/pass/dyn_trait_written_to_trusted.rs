//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/dyn_trait_written_to_trusted.rs`: the trait's contract, which code Thrust
// does not analyze is trusted to keep, is the precondition of a call through the trait object.

#[thrust_macros::context]
trait Call {
    #[thrust_macros::requires(*x < 10)]
    #[thrust_macros::ensures(true)]
    fn call(&self, x: &i64) -> bool;
}

struct S;

impl thrust_models::Model for S {
    type Ty = ();
}

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
    c.call(&5)
}

fn main() {
    run(&S);
}
