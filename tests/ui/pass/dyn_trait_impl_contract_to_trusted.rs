//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/dyn_trait_impl_contract_to_trusted.rs`: `S::call`'s own `requires` holds of
// every argument.

trait Call {
    fn call(&self, x: &i64) -> bool;
}

struct S;

impl thrust_models::Model for S {
    type Ty = ();
}

#[thrust_macros::context]
impl Call for S {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
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
