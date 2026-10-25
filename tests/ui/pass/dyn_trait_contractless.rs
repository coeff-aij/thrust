//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait object may have methods without a contract, as long as they are not called through it.

#[thrust_macros::context]
trait Shape {
    #[thrust_macros::ensures(result >= 3)]
    fn sides(&self) -> u32;

    fn corners(&self) -> u32;
}

struct Tri;

impl thrust_models::Model for Tri {
    type Ty = ();
}

impl Shape for Tri {
    fn sides(&self) -> u32 {
        3
    }

    fn corners(&self) -> u32 {
        3
    }
}

fn min_sides(s: &dyn Shape) -> u32 {
    s.sides()
}

fn main() {
    let t = Tri;
    assert!(min_sides(&t) >= 3 && t.corners() == 3);
}
