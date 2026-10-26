//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Packing at a type parameter in a crate without an invariant, where no type has one.

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
    assert!(s.sides() >= 3);
}
