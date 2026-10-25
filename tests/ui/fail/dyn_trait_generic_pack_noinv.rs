//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The trait's contract gives at least 3 sides through the trait object, not 4.

#[thrust_macros::context]
trait Shape {
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

fn pack<T: Shape + 'static>(x: Box<T>) -> Box<dyn Shape> {
    x
}

fn main() {
    let s = pack(Box::new(Square));
    assert!(s.sides() >= 4);
}
