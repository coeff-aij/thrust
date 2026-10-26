//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The trait's contract does not give 4 sides, which `min_sides` claims.

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

struct Square;

impl thrust_models::Model for Square {
    type Ty = ();
}

impl Shape for Square {
    fn sides(&self) -> u32 {
        4
    }
}

#[thrust_macros::ensures(result >= 4)]
fn min_sides(s: &dyn Shape) -> u32 {
    s.sides()
}

fn main() {
    let t = Tri;
    let q = Square;
    assert!(min_sides(&t) >= 3 && min_sides(&q) >= 3);
}
