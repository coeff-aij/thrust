//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A coercion between trait objects that drops an auto trait keeps the vtable.

#[thrust_macros::context]
trait Shape {
    #[thrust_macros::ensures(result >= 3)]
    fn sides(&self) -> u32;
}

#[thrust_macros::context]
trait Sub: Shape {
    #[thrust_macros::ensures(result >= 1)]
    fn sub(&self) -> u32;
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

impl Sub for Tri {
    fn sub(&self) -> u32 {
        1
    }
}

fn main() {
    let t = Tri;
    let s: &(dyn Shape + Sync) = &t;
    let u: &dyn Shape = s;
    assert!(u.sides() >= 3);
}
