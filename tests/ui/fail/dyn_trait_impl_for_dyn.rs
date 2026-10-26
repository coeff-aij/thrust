//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The impl for `dyn Shape` is checked against `Describe`'s contract at `Self = dyn Shape`: one
// less than `sides`, which is at least 3, need not be at least 3.

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
        self.sides() - 1
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
