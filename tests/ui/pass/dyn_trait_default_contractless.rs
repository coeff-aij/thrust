//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/dyn_trait_default_contractless.rs`: the trait states the contract.

#[thrust_macros::context]
trait Shape {
    #[thrust_macros::ensures(result >= 2)]
    fn sides(&self) -> u32 {
        3
    }
}

struct Sq;

impl thrust_models::Model for Sq {
    type Ty = ();
}

impl Shape for Sq {
    fn sides(&self) -> u32 {
        2
    }
}

fn f(s: &dyn Shape) {
    assert!(s.sides() >= 2);
}

fn main() {
    f(&Sq);
}
