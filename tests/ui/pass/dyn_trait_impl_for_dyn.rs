//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An impl for a trait object (`impl Describe for dyn Shape`) is an ordinary impl, checked at
// `Self = dyn Shape`; a call to it is a static call, not one through the vtable.

#[thrust_macros::context]
trait Shape {
    #[thrust_macros::ensures(result >= 3)]
    fn sides(&self) -> u32;
}

#[thrust_macros::context]
trait Describe {
    #[thrust_macros::ensures(result >= 3)]
    fn describe(&self) -> u32;
}

impl Describe for dyn Shape {
    fn describe(&self) -> u32 {
        self.sides()
    }
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

fn main() {
    let t = Tri;
    let s: &dyn Shape = &t;
    assert!(s.describe() >= 3);
}
