//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `sides` has no contract, so the call resolved to `Sq`'s override takes the override's type,
// inferred from its body, not the default's.
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
fn main() {
    let r = Sq.sides();
    assert!(r == 2);
}
