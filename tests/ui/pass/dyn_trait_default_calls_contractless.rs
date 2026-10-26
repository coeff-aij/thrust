//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/dyn_trait_default_calls_contractless.rs`: the method the default body calls
// through `Self` has a contract on the trait.

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::ensures(result >= 1)]
    fn g(&self) -> u32 {
        5
    }

    #[thrust_macros::ensures(result >= 1)]
    fn h(&self) -> u32 {
        self.g()
    }
}

struct C;

impl thrust_models::Model for C {
    type Ty = ();
}

impl Tr for C {}

fn main() {
    let c = C;
    let d: &dyn Tr = &c;
    assert!(d.h() >= 1);
}
