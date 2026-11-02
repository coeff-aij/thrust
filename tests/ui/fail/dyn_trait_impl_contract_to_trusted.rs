//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The trait gives `call` no contract, so a call through the trait object requires nothing, and
// `S::call` refines that: its own `requires` must hold of every argument, as code Thrust does not
// analyze may call it through the trait object with any.

trait Call {
    fn call(&self, x: &i64) -> bool;
}

struct S;

impl thrust_models::Model for S {
    type Ty = ();
}

#[thrust_macros::context]
impl Call for S {
    #[thrust_macros::requires(*x < 10)]
    #[thrust_macros::ensures(true)]
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
