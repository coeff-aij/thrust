//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `sides` has no contract, so `Sq`'s own contract refines nothing of the trait: the default's
// inferred type is not analyzed at `Sq`, and the call resolved to `Sq` uses `Sq`'s contract.
trait Shape {
    fn sides(&self) -> u32 {
        3
    }
}

struct Sq;

impl thrust_models::Model for Sq {
    type Ty = ();
}

#[thrust_macros::context]
impl Shape for Sq {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == 2)]
    fn sides(&self) -> u32 {
        2
    }
}

fn main() {
    assert!(Sq.sides() == 2);
}
