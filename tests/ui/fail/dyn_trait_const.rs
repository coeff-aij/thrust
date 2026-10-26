//@error-in-other-file: a constant holding a trait object
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A constant holding a trait object is not supported: the coercion that packed it is not
// analyzed.

#[thrust_macros::context]
trait Shape {
    #[thrust_macros::ensures(result >= 3)]
    fn sides(&self) -> u32;
}

struct Tri;

impl thrust_models::Model for Tri {
    type Ty = ();
}

impl Shape for Tri {
    fn sides(&self) -> u32 {
        3
    }
}

const T: &dyn Shape = &Tri;

fn main() {
    let s: &dyn Shape = T;
    assert!(s.sides() >= 3);
}
