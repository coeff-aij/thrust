//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Auto-trait supertraits add no methods to the vtable, so a trait with them is supported as a
// trait object, and its contract holds through it.

#[thrust_macros::context]
trait Shape: Send + Sync {
    #[thrust_macros::ensures(result >= 3)]
    fn sides(&self) -> u32;
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

#[thrust_macros::ensures(result >= 3)]
fn min_sides(s: &dyn Shape) -> u32 {
    s.sides()
}

fn main() {
    let q = Square;
    assert!(min_sides(&q) >= 3);
}
