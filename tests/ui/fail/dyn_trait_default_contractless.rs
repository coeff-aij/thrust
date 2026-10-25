//@error-in-other-file: has no contract on the trait
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A default body's inferred type describes the default only, not an impl that overrides it, so a
// method without a written contract is rejected at a call through `dyn`.

#[thrust_macros::context]
trait Shape {
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
